# Test Runner Benchmark Specification

> Tests covering BenchmarkResult, BenchmarkConfig, Benchmark, BenchmarkSuite, BenchmarkComparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Benchmark Specification

## Scenarios

### BenchmarkResult

<details>
<summary>Advanced: run_benchmark records name and iteration count</summary>

#### run_benchmark records name and iteration count _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual benchmark result evidence (expected show, folded, detail, or skip)


- execute run_benchmark and inspect the returned result
   - Expected: r.name equals `probe`
   - Expected: r.iterations.value equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("execute run_benchmark and inspect the returned result")
val r = run_benchmark("probe", 5, _noop)
expect(r.name).to_equal("probe")
# oracle: run_benchmark ran exactly the 5 requested iterations.
expect(r.iterations.value).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: summary contains the benchmark name and iteration count</summary>

#### summary contains the benchmark name and iteration count _(slow)_

- render a BenchmarkResult summary and check its fields
   - Expected: s contains `named_probe`
   - Expected: s contains `Iterations: 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("render a BenchmarkResult summary and check its fields")
val r = run_benchmark("named_probe", 4, _noop)
val s = r.summary()
expect(s.contains("named_probe")).to_equal(true)
# oracle: summary always reports Iterations line (framework contract).
expect(s.contains("Iterations: 4")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: zero mean time yields zero ops/sec and zero CV</summary>

#### zero mean time yields zero ops/sec and zero CV _(slow)_

- compute derived stats on a zero-timed result
   - Expected: r.ops_per_second() equals `0.0`
   - Expected: r.coefficient_of_variation() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("compute derived stats on a zero-timed result")
val r = BenchmarkResult.new("zeroed")
# oracle: run_benchmark timing is stubbed to 0 ns in the current
# framework, so derived stats must be exactly 0.0, never NaN.
expect(r.ops_per_second()).to_equal(0.0)
expect(r.coefficient_of_variation()).to_equal(0.0)
```

</details>


</details>

### BenchmarkConfig

<details>
<summary>Advanced: presets quick, default, thorough differ in iteration counts</summary>

#### presets quick, default, thorough differ in iteration counts _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual benchmark config evidence (expected show, folded, detail, or skip)


- construct the three config presets and compare them
   - Expected: q.warmup_iterations.value equals `3`
   - Expected: d.iterations.value equals `100`
   - Expected: t.iterations.value equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("construct the three config presets and compare them")
val q = BenchmarkConfig.quick()
val d = BenchmarkConfig.default()
val t = BenchmarkConfig.thorough()
# oracle: fixed preset values from perf.spl (quick 3/20, default
# 10/100, thorough 50/1000 warmup/iterations).
expect(q.warmup_iterations.value).to_equal(3)
expect(d.iterations.value).to_equal(100)
expect(t.iterations.value).to_equal(1000)
```

</details>


</details>

<details>
<summary>Advanced: presets carry their names</summary>

#### presets carry their names _(slow)_

- read the preset names
   - Expected: BenchmarkConfig.quick().name equals `quick`
   - Expected: BenchmarkConfig.thorough().name equals `thorough`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("read the preset names")
# oracle: preset names are part of the public report format.
expect(BenchmarkConfig.quick().name).to_equal("quick")
expect(BenchmarkConfig.thorough().name).to_equal("thorough")
```

</details>


</details>

### Benchmark

<details>
<summary>Advanced: creates benchmark with name and run function</summary>

#### creates benchmark with name and run function _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual benchmark construction evidence (expected show, folded, detail, or skip)


- construct a Benchmark and inspect its fields
   - Expected: b.name equals `bench_a`
   - Expected: b.description_text equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("construct a Benchmark and inspect its fields")
val b = Benchmark.new("bench_a", _noop)
expect(b.name).to_equal("bench_a")
# oracle: fresh benchmark has no description until with_description.
expect(b.description_text).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: builder methods attach description and lifecycle hooks</summary>

#### builder methods attach description and lifecycle hooks _(slow)_

- apply with_description/with_setup/with_teardown and check flags
   - Expected: b.description_text equals `desc`
   - Expected: b.setup_enabled is true
   - Expected: b.teardown_enabled is true
   - Expected: _probe_calls - before equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("apply with_description/with_setup/with_teardown and check flags")
val b0 = Benchmark.new("hooked", _noop)
val b = b0.with_description("desc").with_setup(_probe).with_teardown(_probe)
expect(b.description_text).to_equal("desc")
expect(b.setup_enabled).to_equal(true)
expect(b.teardown_enabled).to_equal(true)
# oracle: setup()/teardown() must actually invoke the attached hooks.
val before = _probe_calls
b.setup()
b.teardown()
expect(_probe_calls - before).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: setup is inert until a hook is attached</summary>

#### setup is inert until a hook is attached _(slow)_

- call setup on a fresh benchmark and observe no probe calls
   - Expected: _probe_calls - before equals `0`
   - Expected: b.setup_enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("call setup on a fresh benchmark and observe no probe calls")
val b = Benchmark.new("bare", _noop)
val before = _probe_calls
b.setup()
# oracle: setup_enabled defaults to false, so no side effect fires.
expect(_probe_calls - before).to_equal(0)
expect(b.setup_enabled).to_equal(false)
```

</details>


</details>

### BenchmarkSuite

<details>
<summary>Advanced: creates suite with name and default config</summary>

#### creates suite with name and default config _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual benchmark suite evidence (expected show, folded, detail, or skip)


- construct a suite and inspect name/config
   - Expected: s.name equals `my_suite`
   - Expected: s.config.name equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("construct a suite and inspect name/config")
val s = BenchmarkSuite.new("my_suite")
expect(s.name).to_equal("my_suite")
# oracle: suites default to the "default" config preset.
expect(s.config.name).to_equal("default")
```

</details>


</details>

<details>
<summary>Advanced: add_fn accumulates runnable benchmarks</summary>

#### add_fn accumulates runnable benchmarks _(slow)_

- add two benchmarks to a suite and count them
   - Expected: s.benchmarks.len() equals `2`
   - Expected: s.benchmarks[1].name equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("add two benchmarks to a suite and count them")
val s = BenchmarkSuite.new("acc")
s.add_fn("first", _noop)
s.add_fn("second", _noop)
# oracle: two adds, two entries, second one named "second".
expect(s.benchmarks.len()).to_equal(2)
expect(s.benchmarks[1].name).to_equal("second")
```

</details>


</details>

<details>
<summary>Advanced: with_config returns a suite carrying the new config</summary>

#### with_config returns a suite carrying the new config _(slow)_

- reconfigure a suite immutably
   - Expected: s.config.name equals `quick`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("reconfigure a suite immutably")
val s = BenchmarkSuite.new("cfg").with_config(BenchmarkConfig.quick())
# oracle: with_config replaces the default preset with "quick".
expect(s.config.name).to_equal("quick")
```

</details>


</details>

### BenchmarkComparison

<details>
<summary>Advanced: compares baseline to current via compare_to</summary>

#### compares baseline to current via compare_to _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual benchmark comparison evidence (expected show, folded, detail, or skip)


- compare two results and read the comparison
   - Expected: cmp.baseline_name equals `base`
   - Expected: cmp.candidate_name equals `cand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("compare two results and read the comparison")
val base = BenchmarkResult.new("base")
val cand = run_benchmark("cand", 3, _noop)
val cmp = base.compare_to(cand)
expect(cmp.baseline_name).to_equal("base")
expect(cmp.candidate_name).to_equal("cand")
```

</details>


</details>

<details>
<summary>Advanced: speedup direction flags agree with the ratio</summary>

#### speedup direction flags agree with the ratio _(slow)_

- check is_faster/is_slower against computed speedup
   - Expected: cmp.speedup equals `0.0`
   - Expected: cmp.is_faster() is false
   - Expected: cmp.is_slower() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("check is_faster/is_slower against computed speedup")
val base = BenchmarkResult.new("base")
val cmp = base.compare_to(base)
# oracle: identical zero-timed results give speedup exactly 0.0
# (0/0 guarded); 0.0 < 1.0 so the contract labels it "slower".
expect(cmp.speedup).to_equal(0.0)
expect(cmp.is_faster()).to_equal(false)
expect(cmp.is_slower()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: summary names both results and a direction</summary>

#### summary names both results and a direction _(slow)_

- render a comparison summary
   - Expected: s contains `b1`
   - Expected: s contains `slower`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TESTRUNNER-BENCH
step("render a comparison summary")
val base = BenchmarkResult.new("b1")
val cmp = base.compare_to(base)
val s = cmp.summary()
expect(s.contains("b1")).to_equal(true)
# oracle: zero speedup is below 1.0, labelled "slower" by contract.
expect(s.contains("slower")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/test_runner_benchmark_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BenchmarkResult, BenchmarkConfig, Benchmark, BenchmarkSuite, BenchmarkComparison.
- BenchmarkResult
- BenchmarkConfig
- Benchmark
- BenchmarkSuite
- BenchmarkComparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 14 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-TESTRUNNER-BENCH`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb77baad98b2768971ed92e6644f9dbc86f3e940f026bd0207368e1e78cbcf9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb77baad98b2768971ed92e6644f9dbc86f3e940f026bd0207368e1e78cbcf9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb77baad98b2768971ed92e6644f9dbc86f3e940f026bd0207368e1e78cbcf9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/perf/test_runner_benchmark_spec.spl
mirror: doc/06_spec/perf/test_runner_benchmark_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/test_runner_benchmark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/test_runner_benchmark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/test_runner_benchmark_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/test_runner_benchmark_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/test_runner_benchmark_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'run_benchmark records name and iteration count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/test_runner_benchmark_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'summary contains the benchmark name and iteration count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/test_runner_benchmark_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero mean time yields zero ops/sec and zero CV' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
