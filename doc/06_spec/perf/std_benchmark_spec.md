# std_benchmark_spec

> Std Benchmark Library Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std_benchmark_spec

Std Benchmark Library Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Testing Infrastructure - Benchmarking |
| Category | Testing \| Performance |
| Status | Active |
| Source | `test/perf/std_benchmark_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Std Benchmark Library Tests

Purpose and audience: verification of the std.benchmark library's config
defaults and time formatting, for engineers running/authoring benchmarks.

Tests for the `std.testing.benchmark` library.
Note: Many benchmark operations chain methods which are not supported
in interpreter mode. Tests use intermediate variables to work around this.

@req REQ-PERF-STD-BENCH
lifecycle: doc/03_plan/sspec_modernization_plan.md ;
           doc/04_architecture/sspec_documentization_maintenance.md

## Scenarios

### Benchmarking Library

<details>
<summary>Advanced: default config has correct warmup</summary>

#### default config has correct warmup _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual std.benchmark library evidence (expected show, folded, detail, or skip)


- verify benchmark library behaviour
   - Expected: config.warmup_iterations equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val config = benchmark_config_default()
# oracle: 3 warmup iterations is the documented default.
expect(config.warmup_iterations).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: default config has correct measurement iterations</summary>

#### default config has correct measurement iterations _(slow)_

- verify benchmark library behaviour
   - Expected: config.measurement_iterations equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val config = benchmark_config_default()
# oracle: 100 measurement iterations is the documented default.
expect(config.measurement_iterations).to_equal(100)
```

</details>


</details>

<details>
<summary>Advanced: default config has correct sample size</summary>

#### default config has correct sample size _(slow)_

- verify benchmark library behaviour
   - Expected: config.sample_size equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val config = benchmark_config_default()
# oracle: 10 samples is the documented default.
expect(config.sample_size).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: quick config has warmup of 1</summary>

#### quick config has warmup of 1 _(slow)_

- verify benchmark library behaviour
   - Expected: config.warmup_iterations equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val config = benchmark_config_quick()
# oracle: quick mode uses a single warmup iteration.
expect(config.warmup_iterations).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: quick config has sample size of 3</summary>

#### quick config has sample size of 3 _(slow)_

- verify benchmark library behaviour
   - Expected: config.sample_size equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val config = benchmark_config_quick()
# oracle: quick mode takes 3 samples.
expect(config.sample_size).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: custom config has correct sample size</summary>

#### custom config has correct sample size _(slow)_

- verify benchmark library behaviour
   - Expected: config.sample_size equals `5`
   - Expected: config.measurement_iterations equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val config = BenchmarkConfig(
    warmup_iterations: 1,
    measurement_iterations: 50,
    sample_size: 5,
    outlier_threshold: 1.5
)
expect(config.sample_size).to_equal(5)
# oracle: custom measurement_iterations echoes through unchanged.
expect(config.measurement_iterations).to_equal(50)
```

</details>


</details>

<details>
<summary>Advanced: calculate_stats computes mean and median of fixed samples</summary>

#### calculate_stats computes mean and median of fixed samples _(slow)_

- verify calculate_stats on a fixed sample set
   - Expected: stats.mean_ns equals `200.0`
   - Expected: stats.median_ns equals `200.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify calculate_stats on a fixed sample set")
# oracle: mean of [100.0, 200.0, 300.0] is exactly 200.0, median too.
val stats = calculate_stats([100.0, 200.0, 300.0], 1.5)
expect(stats.mean_ns).to_equal(200.0)
expect(stats.median_ns).to_equal(200.0)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats nanoseconds</summary>

#### format_time formats nanoseconds _(slow)_

- verify benchmark library behaviour
   - Expected: has_ns is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val result = format_time(500.0)
# oracle: 500.0 ns is below the 1000 ns microsecond boundary.
val has_ns = _text_contains(result, "ns")
expect(has_ns).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats microseconds</summary>

#### format_time formats microseconds _(slow)_

- verify benchmark library behaviour
   - Expected: has_us is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val result = format_time(1500.0)
# oracle: 1500.0 ns is above 1000 ns, below 1 ms.
val has_us = _text_contains(result, "us")
expect(has_us).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats milliseconds</summary>

#### format_time formats milliseconds _(slow)_

- verify benchmark library behaviour
   - Expected: has_ms is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val result = format_time(1500000.0)
# oracle: 1.5e6 ns = 1.5 ms, below the 1 s boundary.
val has_ms = _text_contains(result, "ms")
expect(has_ms).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats seconds</summary>

#### format_time formats seconds _(slow)_

- verify benchmark library behaviour
   - Expected: has_s is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-STD-BENCH
step("verify benchmark library behaviour")
val result = format_time(1500000000.0)
# oracle: 1.5e9 ns = 1.5 s, top formatting tier.
val has_s = _text_contains(result, "s")
expect(has_s).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-STD-BENCH`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd4486fe93fbbfff82999812ae31374d3fe88979a4970677445d05bfc135317d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd4486fe93fbbfff82999812ae31374d3fe88979a4970677445d05bfc135317d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd4486fe93fbbfff82999812ae31374d3fe88979a4970677445d05bfc135317d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/perf/std_benchmark_spec.spl
mirror: doc/06_spec/perf/std_benchmark_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/std_benchmark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/std_benchmark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/std_benchmark_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/std_benchmark_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/std_benchmark_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default config has correct warmup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/std_benchmark_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default config has correct measurement iterations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/std_benchmark_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default config has correct sample size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
