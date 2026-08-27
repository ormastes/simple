# test_runner_benchmark_spec

> Purpose: prove the test runner's REAL benchmark framework

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_runner_benchmark_spec

Purpose: prove the test runner's REAL benchmark framework

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/test_runner_benchmark_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: prove the test runner's REAL benchmark framework
(app.test.bench.bench_harness + app.test.bench.bench_report) measures what it
claims and emits the artifacts consumers read — case/result construction,
warm closure timing (both ns/op and ops/sec rows stay distinct), and the
report/metrics table pair. The original file sketched a BenchmarkResult/
BenchmarkRunner API that does not exist anywhere in src; this rewrite targets
the framework that actually ships. Audience: test-infra and perf owners.

Note: assertions are artifact-based (read the emitted files) because the
interpreter returns Unit for cross-module struct field access — see the
caveat in test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl.

## Scenarios

### test runner bench harness (real framework)

#### warm bench runs the body warmup + iters times

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- warm bench runs the body warmup + iters times
   - Expected: _workload_counter equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("warm bench runs the body warmup + iters times")
val bc = make_bench_case("counter_case", "interp", "warm", 4)
_workload_counter = 0
val _r = bench_run_warm(bc, _counting_workload)
# oracle: 1 warmup call + 4 timed iterations = exactly 5 invocations
expect(_workload_counter).to_equal(5)
```

</details>

#### warm bench emits distinct ops/sec and ns/op rows

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- warm bench emits distinct ops/sec and ns/op rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("warm bench emits distinct ops/sec and ns/op rows")
_reset_artifacts()
val bc = make_bench_case("dual_row_case", "interp", "warm", 3)
val r_ops = bench_run_warm(bc, _counting_workload)
val r_ns = bench_run_warm_ns(bc, _counting_workload)
var rows: [BenchResult] = []
rows.push(r_ops)
rows.push(r_ns)
bench_emit(rows, REPORT_PATH, TABLE_PATH)
val report = _read_file(REPORT_PATH)
# oracle: both metric kinds appear as separate rows, never collapsed
expect(report).to_contain("ops/sec")
expect(report).to_contain("ns/op")
```

</details>

#### bench_emit writes both the report and the metrics table

- bench_emit writes both the report and the metrics table
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: rt_file_exists(REPORT_PATH) is true
   - Expected: rt_file_exists(TABLE_PATH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("bench_emit writes both the report and the metrics table")
_reset_artifacts()
var rows: [BenchResult] = []
rows.push(make_bench_result("emit_case", "interp", "warm", "ns/op", 42, "ns/op"))
bench_emit(rows, REPORT_PATH, TABLE_PATH)
# oracle: both consumer-facing artifacts exist after emit
expect(rt_file_exists(REPORT_PATH)).to_equal(true)
expect(rt_file_exists(TABLE_PATH)).to_equal(true)
```

</details>

#### emitted rows carry the case name and arch tag

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- emitted rows carry the case name and arch tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("emitted rows carry the case name and arch tag")
_reset_artifacts()
var rows: [BenchResult] = []
rows.push(make_bench_result("tagged_case_x86", "interp", "warm", "ns/op", 7, "ns/op"))
bench_emit(rows, REPORT_PATH, TABLE_PATH)
val table = _read_file(TABLE_PATH)
# oracle: the row is traceable to its benchmark name and arch lane
expect(table).to_contain("tagged_case_x86")
expect(table).to_contain("x86_64")
```

</details>

#### process-plane row measures a real child process

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- process-plane row measures a real child process


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("process-plane row measures a real child process")
_reset_artifacts()
val bc = make_bench_case("proc_case", "script", "process", 1)
val r = bench_run_process(bc, ["/bin/echo", "bench_probe"])
var rows: [BenchResult] = []
rows.push(r)
bench_emit(rows, REPORT_PATH, TABLE_PATH)
val report = _read_file(REPORT_PATH)
# oracle: the wall_ms metric row for the measured child exists
expect(report).to_contain("wall_ms")
expect(report).to_contain("proc_case")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
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

- Canonical SPipe generation for source `e5c323d6f1948962e1ed60f53b71c5188acebc6411e3fb1ad8c32a1d92eb5f98`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5c323d6f1948962e1ed60f53b71c5188acebc6411e3fb1ad8c32a1d92eb5f98`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5c323d6f1948962e1ed60f53b71c5188acebc6411e3fb1ad8c32a1d92eb5f98`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/05_perf/test_runner_benchmark_spec.spl
mirror: doc/06_spec/05_perf/test_runner_benchmark_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/test_runner_benchmark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/test_runner_benchmark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/test_runner_benchmark_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
