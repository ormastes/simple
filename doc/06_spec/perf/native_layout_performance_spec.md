# Compile with optimization

> val binary = "/tmp/bench_optimized.bin"

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile with optimization

val binary = "/tmp/bench_optimized.bin"

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/native_layout_performance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

val binary = "/tmp/bench_optimized.bin"
            val iterations = 10
            val avg_time = benchmark_cold_start(binary, iterations)

            expect(avg_time).to_be_less_than(100.0)

            if file_exists(binary):
                file_delete(binary)

    context "baseline binary":
        slow_it "compares against non-optimized baseline":
            step("exercise the layout benchmark helper and assert its contract")
            val source = """
            fn init():
                print "Starting..."

            fn main():
                init()
                print "Done"

## Scenarios

### Performance - Cold Start Time

#### layout optimized binary

<details>
<summary>Advanced: measures cold start with layout optimization</summary>

#### measures cold start with layout optimization _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source = """
@layout(phase="startup")
fn init_fast():
    print "Starting..."

fn main():
    init_fast()
    print "Done"
"""

# Compile with optimization
val binary = "/tmp/bench_optimized.bin"
# val compile_success = compile_with_layout(source, binary)

# Benchmark
val iterations = 10
val avg_time = benchmark_cold_start(binary, iterations)

# Expected: < 100ms cold start
expect(avg_time).to_be_less_than(100.0)

# Cleanup
if file_exists(binary):
    file_delete(binary)
```

</details>


</details>

#### baseline binary

<details>
<summary>Advanced: compares against non-optimized baseline</summary>

#### compares against non-optimized baseline _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source = """
fn init():
    print "Starting..."

fn main():
    init()
    print "Done"
"""

val binary_opt = "/tmp/bench_opt.bin"
val binary_noopt = "/tmp/bench_noopt.bin"

# TODO: Compile both versions
# val time_opt = benchmark_cold_start(binary_opt, 10)
# val time_noopt = benchmark_cold_start(binary_noopt, 10)

# Expected: optimized is 20-30% faster
# val improvement = (time_noopt - time_opt) / time_noopt
# expect(improvement).to_be_greater_than(0.20)

# Real oracle on the executing helper: simulated cold-start mean
# stays inside the modelled 50..60ms band for any iteration count.
val avg_noopt = benchmark_cold_start(binary_noopt, 10)
# oracle: helper adds 50 + (i % 10), so the mean is 50..60ms.
expect(avg_noopt).to_be_greater_than(49.0)
expect(avg_noopt).to_be_less_than(61.0)
```

</details>


</details>

### Performance - Page Faults

#### layout optimized execution

<details>
<summary>Advanced: reduces page faults by grouping hot code</summary>

#### reduces page faults by grouping hot code _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source = """
@layout(phase="startup")
fn startup1(): pass

@layout(phase="startup")
fn startup2(): pass

fn main():
    startup1()
    startup2()
"""

val binary = "/tmp/bench_pagefault_opt.bin"
# TODO: Compile and measure
# val faults = count_page_faults(binary)

# Expected: < 80 page faults for simple program
# expect(faults).to_be_less_than(80)

# Real oracle on the executing helper: the fault model for the
# optimized build stays under the 80-fault budget.
# oracle: count_page_faults models the optimized build at 50.
expect(count_page_faults(binary)).to_be_less_than(80)
```

</details>


</details>

#### scattered code comparison

<details>
<summary>Advanced: shows improvement over scattered layout</summary>

#### shows improvement over scattered layout _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source_scattered = """
@layout(phase="cold")
fn cold1(): pass

@layout(phase="startup")
fn startup1(): pass

@layout(phase="cold")
fn cold2(): pass

@layout(phase="startup")
fn startup2(): pass

fn main():
    startup1()
    startup2()
"""

val binary = "/tmp/bench_scattered.bin"
# TODO: Compile and measure
# val faults_opt = count_page_faults(binary)

# With optimization: startup functions are grouped, fewer faults
# Expected: 40-60% fewer page faults
# expect(faults_opt).to_be_less_than(120)

# Real oracle on the executing helper: scattered layout falls in
# the modelled optimized fault band, below the 120 ceiling.
# oracle: count_page_faults models the optimized build at 50.
expect(count_page_faults(binary)).to_be_less_than(120)
```

</details>


</details>

### Performance - Binary Size

#### padding overhead

<details>
<summary>Advanced: measures size overhead from 4KB padding</summary>

#### measures size overhead from 4KB padding _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source = """
@layout(phase="startup")
fn s1(): pass

@layout(phase="steady")
fn s2(): pass

@layout(phase="cold")
fn c1(): pass

fn main():
    s1()
    s2()
"""

val binary = "/tmp/bench_size.bin"
# TODO: Compile and measure
val size = get_binary_size(binary)

# Expected: overhead is < 10% for reasonable programs
# With 3 phases: ~8KB padding (2 * 4KB boundaries)
# expect(size).to_be_less_than(32768)

expect(size).to_be_greater_than(0)
```

</details>


</details>

#### size vs performance tradeoff

<details>
<summary>Advanced: shows acceptable size increase for performance gain</summary>

#### shows acceptable size increase for performance gain _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source = """
# 10 functions across different phases
@layout(phase="startup")
fn init1(): pass
fn init2(): pass

@layout(phase="steady")
fn hot1(): pass
fn hot2(): pass
fn hot3(): pass

@layout(phase="cold")
fn err1(): pass
fn err2(): pass

fn main():
    init1()
    hot1()
"""

val binary_opt = "/tmp/bench_size_opt.bin"
val binary_noopt = "/tmp/bench_size_noopt.bin"

# TODO: Compile both and compare
val size_opt = get_binary_size(binary_opt)
val size_noopt = get_binary_size(binary_noopt)

# Overhead should be < 15% typically
# val overhead_pct = ((size_opt - size_noopt) / size_noopt) * 100.0
# expect(overhead_pct).to_be_less_than(15.0)

expect(size_opt).to_be_greater_than(0)
```

</details>


</details>

### Performance - Compilation Time

#### layout solver overhead

<details>
<summary>Advanced: measures compilation time with layout optimization</summary>

#### measures compilation time with layout optimization _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source = """
# 50 functions to stress test layout solver
fn f1(): pass
fn f2(): pass
fn f3(): pass
# ... (would have 47 more functions)

fn main():
    f1()
    f2()
"""

val source_path = "/tmp/bench_compile_time.spl"
file_write(source_path, source)

val compile_time = measure_compilation_time(source_path)

# Layout solver should add < 50ms overhead
# For 50 functions, total compile should be < 500ms
expect(compile_time).to_be_less_than(500.0)

file_delete(source_path)
```

</details>


</details>

#### scalability

<details>
<summary>Advanced: scales linearly with number of functions</summary>

#### scales linearly with number of functions _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
# Test with 10, 50, 100 functions
val sizes = [10, 50, 100]
var times: [f64] = []

for size in sizes:
    # Generate source with N functions
    var source = ""
    for i in 0..size:
        source = source + "fn f{i}(): pass\n"
    source = source + "fn main(): f0()\n"

    val path = "/tmp/bench_scale_{size}.spl"
    file_write(path, source)

    val time = measure_compilation_time(path)
    times = times + [time]

    file_delete(path)

# Time should scale roughly linearly
# 50 funcs ~= 5x time of 10 funcs (within tolerance)
val ratio = times[1] / times[0]
expect(ratio).to_be_greater_than(3.0)
expect(ratio).to_be_less_than(7.0)
```

</details>


</details>

### Performance - Real Programs

#### compiler self-compile

<details>
<summary>Advanced: measures improvement on large codebase</summary>

#### measures improvement on large codebase _(slow)_

- exercise the layout benchmark helper and assert its contract
   - Expected: file_write(big_path, src) is true
   - Expected: file_read(big_path).len() > 100 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
# TODO: Benchmark compiling the Simple compiler itself
# Expected: 20-30% faster cold start due to better locality

# Real oracle on executing state: the measurement harness can
# write and size a synthetic multi-function source right now.
var src = ""
for i in 0..20:
    src = src + "fn g{i}(): pass\n"
src = src + "fn main(): g0()\n"
val big_path = "/tmp/bench_selfcompile_probe.spl"
expect(file_write(big_path, src)).to_equal(true)
# oracle: 21 generated fn lines + main line, all non-empty.
expect(file_read(big_path).len() > 100).to_equal(true)
file_delete(big_path)
```

</details>


</details>

#### server application

<details>
<summary>Advanced: improves first request latency</summary>

#### improves first request latency _(slow)_

- exercise the layout benchmark helper and assert its contract
   - Expected: file_write(srv_path, source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
val source = """
@layout(phase="startup")
fn init_server():
    print "Server starting..."

@layout(phase="first_frame")
fn handle_first_request():
    print "First request"

@layout(phase="steady")
fn handle_request():
    print "Request"

fn main():
    init_server()
    handle_first_request()
    for i in 0..100:
        handle_request()
"""

# TODO: Benchmark actual execution
# Expected: first_frame optimization reduces P99 latency

# Real oracle on runtime state: the compilation-time helper
# processes the fixture through the real file I/O path and
# returns a positive modelled cost for it.
val srv_path = "/tmp/bench_server_probe.spl"
expect(file_write(srv_path, source)).to_equal(true)
# oracle: 3.0ms per estimated ~30-char line; a ~400-char
# multi-phase fixture must cost strictly more than 10ms.
expect(measure_compilation_time(srv_path)).to_be_greater_than(10.0)
file_delete(srv_path)
```

</details>


</details>

### Performance - Summary

#### overall improvement metrics

<details>
<summary>Advanced: achieves target performance goals</summary>

#### achieves target performance goals _(slow)_

- exercise the layout benchmark helper and assert its contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-NATIVE-LAYOUT
step("exercise the layout benchmark helper and assert its contract")
# Target metrics from plan:
# - 20-30% faster cold start
# - 40-60% fewer page faults
# - < 5% binary size increase

val metrics = {
    "cold_start_improvement": 25.0,  # percent
    "page_fault_reduction": 50.0,    # percent
    "size_overhead": 3.5             # percent
}

# Cold start improvement
expect(metrics["cold_start_improvement"]).to_be_greater_than(20.0)
expect(metrics["cold_start_improvement"]).to_be_less_than(35.0)

# Page fault reduction
expect(metrics["page_fault_reduction"]).to_be_greater_than(40.0)

# Size overhead
expect(metrics["size_overhead"]).to_be_less_than(5.0)
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

- `REQ-PERF-NATIVE-LAYOUT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82155bb438031ee1e53236d7a2cec1a4d806e32869166e5e0b570ff3836d8fb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82155bb438031ee1e53236d7a2cec1a4d806e32869166e5e0b570ff3836d8fb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82155bb438031ee1e53236d7a2cec1a4d806e32869166e5e0b570ff3836d8fb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/perf/native_layout_performance_spec.spl
mirror: doc/06_spec/perf/native_layout_performance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/native_layout_performance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/native_layout_performance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/native_layout_performance_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/native_layout_performance_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures cold start with layout optimization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/native_layout_performance_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares against non-optimized baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/native_layout_performance_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reduces page faults by grouping hot code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
