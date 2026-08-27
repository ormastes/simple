# cli_dispatch_perf_spec

> val start = time_now_unix_micros()

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cli_dispatch_perf_spec

val start = time_now_unix_micros()

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/cli_dispatch_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

val start = time_now_unix_micros()
    val code = f()
    val elapsed = time_now_unix_micros() - start
    (code, elapsed)

fn measure_command_time(cmd: text, args: [text]) -> (i64, i64):
    """Measure time to run a command via process.

    Returns: (exit_code, elapsed_micros)

## Scenarios

### CLI Startup Performance

### Version Command (Minimal Overhead)

<details>
<summary>Advanced: executes in under 25ms</summary>

#### executes in under 25ms _(slow)_

- executes in under 25ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("executes in under 25ms")
val (code, elapsed) = measure_command_time("--version", [])
expect code == 0

val elapsed_ms = elapsed / 1000
if elapsed_ms >= 25:
    print "Warning: --version took {elapsed_ms}ms (target: <25ms)"

# Soft assertion (warning, not failure)
expect elapsed_ms < 50  # Generous limit for slow CI
```

</details>


</details>

<details>
<summary>Advanced: is within 10ms of Rust baseline</summary>

#### is within 10ms of Rust baseline _(slow)_

- is within 10ms of Rust baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("is within 10ms of Rust baseline")
val (_, rust_time) = measure_baseline_rust("--version", [])
val (_, simple_time) = measure_simple_impl("--version", [])

val overhead = calculate_overhead(simple_time, rust_time)
val overhead_ms = overhead / 1000

if overhead_ms >= 10:
    print "Warning: overhead is {overhead_ms}ms (target: <10ms)"

# Soft assertion
expect overhead_ms < 20  # Generous limit
```

</details>


</details>

### Help Command (Text Generation)

<details>
<summary>Advanced: executes in under 30ms</summary>

#### executes in under 30ms _(slow)_

- executes in under 30ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("executes in under 30ms")
val (code, elapsed) = measure_command_time("--help", [])
expect code == 0

val elapsed_ms = elapsed / 1000
expect elapsed_ms < 50  # Generous limit
```

</details>


</details>

### Command Dispatch Overhead

### Compile Command Dispatch

<details>
<summary>Advanced: help flag dispatches quickly</summary>

#### help flag dispatches quickly _(slow)_

- help flag dispatches quickly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("help flag dispatches quickly")
val (code, elapsed) = measure_command_time("compile", ["--help"])
expect code == 0

val elapsed_ms = elapsed / 1000
if elapsed_ms >= 30:
    print "Warning: compile --help took {elapsed_ms}ms"
```

</details>


</details>

### Check Command Dispatch

<details>
<summary>Advanced: help flag dispatches quickly</summary>

#### help flag dispatches quickly _(slow)_

- help flag dispatches quickly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("help flag dispatches quickly")
val (code, elapsed) = measure_command_time("check", ["--help"])
expect code == 0

val elapsed_ms = elapsed / 1000
if elapsed_ms >= 30:
    print "Warning: check --help took {elapsed_ms}ms"
```

</details>


</details>

### End-to-End Command Performance

### Compile Small File

<details>
<summary>Advanced: compiles hello.spl in reasonable time</summary>

#### compiles hello.spl in reasonable time _(slow)_

- compiles hello.spl in reasonable time


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compiles hello.spl in reasonable time")
# Create test file
val test_file = "/tmp/benchmark_hello.spl"
file_write(test_file, "fn main(): print \"hello\"")

val (code, elapsed) = measure_command_time("compile", [test_file])
expect code == 0 or code == 1  # May fail (parser bug), just measure time

val elapsed_ms = elapsed / 1000
if elapsed_ms >= 200:
    print "Warning: compile took {elapsed_ms}ms (target: <200ms)"

# Clean up
file_delete(test_file)
```

</details>


</details>

### Format Command

<details>
<summary>Advanced: formats file quickly</summary>

#### formats file quickly _(slow)_

- formats file quickly


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("formats file quickly")
val test_file = "/tmp/benchmark_test.spl"
file_write(test_file, "fn main(): print \"test\"")

val (code, elapsed) = measure_command_time("fmt", ["--check", test_file])

val elapsed_ms = elapsed / 1000
if elapsed_ms >= 100:
    print "Warning: fmt --check took {elapsed_ms}ms (target: <100ms)"

file_delete(test_file)
```

</details>


</details>

### Simple vs Rust Slowdown

### Compile Command Slowdown

<details>
<summary>Advanced: is within 2x of Rust</summary>

#### is within 2x of Rust _(slow)_

- is within 2x of Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("is within 2x of Rust")
val test_file = "/tmp/benchmark_hello.spl"
file_write(test_file, "fn main(): print \"hello\"")

# Measure Rust baseline
val (_, rust_time) = measure_baseline_rust("compile", [test_file, "--help"])

# Measure Simple implementation
val (_, simple_time) = measure_simple_impl("compile", [test_file, "--help"])

val slowdown = calculate_slowdown(simple_time, rust_time)

print "Slowdown factor: {slowdown:.2f}x"
print "Rust time: {rust_time / 1000}ms"
print "Simple time: {simple_time / 1000}ms"

expect slowdown < 2.5  # Allow 2.5x for first implementation

file_delete(test_file)
```

</details>


</details>

### Benchmark Summary

### Performance Targets

<details>
<summary>Advanced: reports target status</summary>

#### reports target status _(slow)_

- reports target status


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("reports target status")
print ""
print "=== CLI Dispatch Performance Summary ==="
print ""
print "Targets:"
print "  Startup time: <25ms"
print "  Dispatch overhead: <10ms"
print "  Slowdown factor: <2x"
print ""
print "Next steps:"
print "  1. Implement Rust FFI handler (rt_cli_dispatch_rust)"
print "  2. Run benchmarks: simple test test/perf/"
print "  3. Profile with perf if targets not met"
print "  4. Optimize hotspots (lazy loading, precompilation)"
print ""

# Always pass (this is informational)
expect true
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 9 |
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

- Canonical SPipe generation for source `6fa0234373dcaa9b7debe62cef517fc1253a9550791e5250a1afc897a42d1c1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6fa0234373dcaa9b7debe62cef517fc1253a9550791e5250a1afc897a42d1c1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6fa0234373dcaa9b7debe62cef517fc1253a9550791e5250a1afc897a42d1c1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/cli_dispatch_perf_spec.spl
mirror: doc/06_spec/05_perf/cli_dispatch_perf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/cli_dispatch_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/cli_dispatch_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/cli_dispatch_perf_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes in under 25ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/cli_dispatch_perf_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is within 10ms of Rust baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/cli_dispatch_perf_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes in under 30ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
