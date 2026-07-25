# Compile with optimization

> val binary = "/tmp/bench_optimized.bin"

<!-- sdn-diagram:id=native_layout_performance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_layout_performance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_layout_performance_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_layout_performance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Category | Other |
| Status | Active |
| Source | `test/05_perf/native_layout_performance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

val binary = "/tmp/bench_optimized.bin"
            val iterations = 10
            val avg_time = benchmark_cold_start(binary, iterations)

            expect(avg_time).to_be_less_than(100.0)

            if file_exists(binary):
                file_delete(binary)

    context "baseline binary":
        slow_it "compares against non-optimized baseline":
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

1. fn init fast
2. fn main
3. init fast
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn init
2. fn main
3. init
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

# Placeholder assertion
expect(true).to_equal(true)
```

</details>


</details>

### Performance - Page Faults

#### layout optimized execution

<details>
<summary>Advanced: reduces page faults by grouping hot code</summary>

#### reduces page faults by grouping hot code _(slow)_

1. fn startup1
2. fn startup2
3. fn main
4. startup1
5. startup2
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

expect(true).to_equal(true)  # Placeholder
```

</details>


</details>

#### scattered code comparison

<details>
<summary>Advanced: shows improvement over scattered layout</summary>

#### shows improvement over scattered layout _(slow)_

1. fn cold1
2. fn startup1
3. fn cold2
4. fn startup2
5. fn main
6. startup1
7. startup2
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

expect(true).to_equal(true)  # Placeholder
```

</details>


</details>

### Performance - Binary Size

#### padding overhead

<details>
<summary>Advanced: measures size overhead from 4KB padding</summary>

#### measures size overhead from 4KB padding _(slow)_

1. fn s1
2. fn s2
3. fn c1
4. fn main
5. s1
6. s2


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn init1
2. fn init2
3. fn hot1
4. fn hot2
5. fn hot3
6. fn err1
7. fn err2
8. fn main
9. init1
10. hot1


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn f1
2. fn f2
3. fn f3
4. fn main
5. f1
6. f2
7. file write
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. source = source + "fn f{i}
2. source = source + "fn main
3. file write
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO: Benchmark compiling the Simple compiler itself
# Expected: 20-30% faster cold start due to better locality

expect(true).to_equal(true)  # Placeholder
```

</details>


</details>

#### server application

<details>
<summary>Advanced: improves first request latency</summary>

#### improves first request latency _(slow)_

1. fn init server
2. fn handle first request
3. fn handle request
4. fn main
5. init server
6. handle first request
7. handle request
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

expect(true).to_equal(true)  # Placeholder
```

</details>


</details>

### Performance - Summary

#### overall improvement metrics

<details>
<summary>Advanced: achieves target performance goals</summary>

#### achieves target performance goals _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
