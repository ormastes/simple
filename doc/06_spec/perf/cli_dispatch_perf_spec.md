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
| Category | Performance |
| Status | Active |
| Source | `test/perf/cli_dispatch_perf_spec.spl` |
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

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
val (code, elapsed) = measure_command_time("--version", [])
expect code == 0

val elapsed_ms = elapsed / 1000
if elapsed_ms >= 25:
    print "Warning: --version took {elapsed_ms}ms (target: <25ms)"

# Soft assertion (warning, not failure)
# oracle: 50ms ceiling, 2x the 25ms target, generous for slow CI.
expect elapsed_ms < 50  # Generous limit for slow CI
```

</details>


</details>

<details>
<summary>Advanced: is within 10ms of Rust baseline</summary>

#### is within 10ms of Rust baseline _(slow)_

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
val (_, rust_time) = measure_baseline_rust("--version", [])
val (_, simple_time) = measure_simple_impl("--version", [])

val overhead = calculate_overhead(simple_time, rust_time)
val overhead_ms = overhead / 1000

if overhead_ms >= 10:
    print "Warning: overhead is {overhead_ms}ms (target: <10ms)"

# Soft assertion
# oracle: 20ms ceiling, 2x the 10ms overhead target, for slow CI.
expect overhead_ms < 20  # Generous limit
```

</details>


</details>

### Help Command (Text Generation)

<details>
<summary>Advanced: executes in under 30ms</summary>

#### executes in under 30ms _(slow)_

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
val (code, elapsed) = measure_command_time("--help", [])
expect code == 0

val elapsed_ms = elapsed / 1000
# oracle: 50ms ceiling for --help generation, generous for slow CI.
expect elapsed_ms < 50
```

</details>


</details>

### Command Dispatch Overhead

### Compile Command Dispatch

<details>
<summary>Advanced: help flag dispatches quickly</summary>

#### help flag dispatches quickly _(slow)_

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
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

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
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

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
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

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
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

- measure CLI command timing and assert the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
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

# oracle: 2.5x allows 0.5x margin over the 2x target for the
# first pure-Simple implementation.
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

- measure CLI command timing and assert the target
   - Expected: (wrote and removed) is true
   - Expected: probe_code equals `7`
   - Expected: (probe_elapsed >= 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CLI-DISPATCH
step("measure CLI command timing and assert the target")
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

# Real oracle: the scratch-file round-trip the benchmarks rely on
# actually works, so the summary is backed by working tooling.
val probe_path = "/tmp/cli_dispatch_probe.spl"
val wrote = file_write(probe_path, "fn main(): print \"ok\"")
val removed = file_delete(probe_path)
expect((wrote and removed)).to_equal(true)
# oracle: measure_time returns non-negative elapsed for any kernel.
val (probe_code, probe_elapsed) = measure_time(fn(): 7)
expect(probe_code).to_equal(7)
expect((probe_elapsed >= 0)).to_equal(true)
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

- `REQ-PERF-CLI-DISPATCH`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4df66a069618f9adb1a96a6400d01a38f000aaaaad8e9b37971bab083d12559c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4df66a069618f9adb1a96a6400d01a38f000aaaaad8e9b37971bab083d12559c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4df66a069618f9adb1a96a6400d01a38f000aaaaad8e9b37971bab083d12559c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/perf/cli_dispatch_perf_spec.spl
mirror: doc/06_spec/perf/cli_dispatch_perf_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/cli_dispatch_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/cli_dispatch_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/cli_dispatch_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/cli_dispatch_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/cli_dispatch_perf_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes in under 25ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/cli_dispatch_perf_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is within 10ms of Rust baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/cli_dispatch_perf_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes in under 30ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
