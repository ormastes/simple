# Benchmarking Guide

Statistical performance measurement and test optimization for Simple.

---

## Table of Contents

1. [Quick Start](#quick-start)
2. [Configuration](#configuration)
3. [Understanding Results](#understanding-results)
4. [Comparison Mode](#comparison-mode)
5. [Integration with SPipe](#integration-with-spipe)
6. [Optimization Patterns](#optimization-patterns)
7. [CI/CD Integration](#cicd-integration)
8. [API Reference](#api-reference)
9. [Troubleshooting](#troubleshooting)

---

## Quick Start

**Library:** `std.testing.benchmark`

### Basic Benchmark

```simple
import std.testing.benchmark as bench

fn main():
    val stats = bench.benchmark_default("fibonacci", \:
        fibonacci(30)
    )
    print stats.summary()
```

Output:

```
Mean:     145.23 ms +/- 2.31 ms
Median:   144.98 ms
Range:    [142.11 ms .. 151.45 ms]
Outliers: 0 low, 1 high
Samples:  10
```

### Compare Implementations

```simple
val data = generate_random_list(10000)

val results = bench.compare_default({
    "quicksort": \: quicksort(data.clone()),
    "mergesort": \: mergesort(data.clone()),
    "heapsort": \: heapsort(data.clone())
})

for (name, stats) in results:
    print "{name}: {stats.summary()}"
```

---

## Configuration

### Presets

```simple
val config = BenchmarkConfig.default()
# warmup_iterations: 3, measurement_iterations: 100
# measurement_time_secs: 5.0, sample_size: 10
# outlier_threshold: 3.0, confidence_level: 0.95

val config = BenchmarkConfig.quick()
# warmup_iterations: 1, measurement_iterations: 50
# measurement_time_secs: 2.0, sample_size: 3
```

### Custom Configuration

```simple
val config = BenchmarkConfig(
    warmup_iterations: 5,
    measurement_iterations: 200,
    measurement_time_secs: 10.0,
    sample_size: 20,
    outlier_threshold: 2.5,
    confidence_level: 0.99
)

val stats = bench.benchmark("custom", \: my_function(), config)
```

---

## Understanding Results

### Statistics

| Metric | Description | Notes |
|--------|-------------|-------|
| **Mean** | Average execution time | Affected by outliers |
| **Median** | Middle value when sorted | More robust than mean |
| **Standard Deviation** | Measure of variability | Lower is better |
| **Outliers (low)** | Unusually fast runs | Cache hits, etc. |
| **Outliers (high)** | Unusually slow runs | GC, context switches |

### Interpreting Outliers

- **0 outliers** -- Very consistent performance
- **1-2 outliers** -- Normal variation
- **3+ outliers** -- Investigate: GC pauses, OS context switches, cache misses, thermal throttling

---

## Comparison Mode

Always clone data for fair comparison:

```simple
val data = generate_large_dataset()

# Good: Each implementation gets fresh data
val results = bench.compare_default({
    "in_place": \: sort_in_place(data.clone()),
    "copy": \: sort_copy(data.clone())
})

# Bad: Second gets pre-sorted data
val results = bench.compare_default({
    "first": \: sort(data),
    "second": \: sort(data)  # Already sorted!
})
```

Find the fastest:

```simple
var fastest_name = ""
var fastest_time = f64.MAX
for (name, stats) in results:
    if stats.mean_ns < fastest_time:
        fastest_time = stats.mean_ns
        fastest_name = name
print "Fastest: {fastest_name}"
```

### Native Backend Parity

For host-native compiler/backend checks, use the net-driver arithmetic parity
benchmark. It builds the C reference with `gcc -O3 -march=native`, builds the
Simple native benchmark with aggressive optimization, runs both, and verifies
that checksum labels match:

```bash
test/05_perf/run_net_driver_logic_parity_bench.shs
```

To check both Simple native backends explicitly, compile
`test/05_perf/net_driver_logic_native_bench.spl` with `--backend=cranelift` and
`--backend=llvm`; both binaries should print the same 11 `virt...` checksum
labels.

### Generated 2D Backend Readback Matrix

Use the generated 2D backend matrix wrapper when changing Engine2D readback,
backend measurement export, or Simple Web layout evidence paths:

```bash
sh scripts/check/check-generated-2d-backend-readback-matrix-evidence.shs
```

The wrapper runs CUDA, OpenCL, Vulkan, Metal, and ROCm lanes. By default,
Linux requires CUDA/OpenCL/Vulkan and macOS also requires Metal; override with
`GENERATED_2D_REQUIRED_BACKENDS` for host-specific probes. Required lanes
auto-prepare missing portable CUDA/Metal/ROCm toolchain artifacts through
`scripts/check/check-portable-compute-toolchains.shs`, then must pass exact
checksum/readback proof with a zero child exit code and must expose normalized device proof:
`submit_attempted=true`, `readback_available=true`, positive matching aggregate checksums,
positive matching per-op checksums for CUDA/OpenCL/Metal/ROCm,
exercised ops, `backend_name=<backend>`, and `clear`/`rect` status, checksum, and
zero-mismatch proof for the Vulkan lane, and the backend proof path. Unavailable optional lanes are recorded as explicit
host-unavailable evidence instead of hidden success. The companion report is
written under `doc/09_report/`, and per-backend logs/evidence files are written
under `build/generated_2d_backend_readback_matrix/`.

The portable toolchain wrapper executes the Simple emitter through a delimited
SPipe payload and validates that every required entry symbol is present before
invoking a native compiler. It must not substitute shell-authored CUDA, OpenCL,
or Metal source. On Metal, scalar arguments use `constant T& [[buffer(n)]]`
bindings after the storage buffers. Metal validation deliberately records two
separate proofs: native `metal`/`metallib` tools build and inspect a metallib,
while the runtime harness independently compiles the current generated Simple
source through the stdlib Metal SFFI facade (it does not load that metallib).
The harness uploads a non-uniform host buffer plus scalar parameters, submits
and waits for fill/copy/alpha/scroll kernels, then downloads device buffers and
compares position-sensitive hashes. It checks every bind, dispatch, encoder,
commit, wait, upload, and download result; `submit_attempted=true` is emitted
only after a command buffer commit succeeds. Empty
source, missing tools, compiler failure, invalid artifact magic, missing entry
symbols, absent submission, or unavailable readback are all fail-closed.

Use `sh scripts/check/check-generated-2d-backend-readback-matrix-evidence.shs
--self-test` after changing the wrapper. It uses fake child lanes to prove a
backend cannot report `pass` unless submit/readback provenance, positive
matching aggregate and per-op checksums, exercised ops, zero mismatches, and a zero child exit code are present.
For Vulkan, the aggregate also rejects evidence whose backend name is not exactly
`vulkan` or whose `clear`/`rect` per-op proof is incomplete. For CUDA, OpenCL,
Metal, and ROCm, the aggregate rejects evidence whose `backend_name` is missing
or names a different backend.
For Metal-specific parser changes, also run
`sh scripts/check/check-metal-generated-2d-readback.shs --self-test`.
For CUDA-specific parser changes, also run
`sh scripts/check/check-cuda-generated-2d-readback.shs --self-test`. CUDA PASS
evidence also requires a positive stable UUID-derived device identity.
The aggregate matrix additionally requires the CUDA backend report to exist and
be nonempty; source tokens alone are not PASS evidence.
For OpenCL-specific parser changes, also run
`sh scripts/check/check-opencl-generated-2d-readback.shs --self-test`.
For ROCm-specific parser changes, also run
`sh scripts/check/check-rocm-generated-2d-readback.shs --self-test`.
For Vulkan-specific parser changes, also run
`sh scripts/check/check-vulkan-engine2d-readback.shs --self-test`.

For Simple Web layout benchmark scenes, the Node bitmap fixture can consume a
Simple-produced ARGB transport baseline with
`SIMPLE_WEB_ENGINE2D_BASELINE_ARGB_IN`. This keeps live Electron/Node capture
checks exact. The forced DOM text-flow gate is now part of the exact evidence
set: `ELECTRON_LAYOUT_CAPTURE_MODE=dom sh
scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs` must report
`mismatch_count=0` without blur or tolerance.

For the production GUI renderer slice, use the aggregate wrapper:

```bash
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

Use the checked in-tree Simple binary, or pass `SIMPLE_BIN=...` when the lane
requires a specific compiler/runtime build. PATH discovery is intentionally not
automatic for production parity evidence: the Electron generated-GUI and layout
wrappers require `ALLOW_PATH_SIMPLE_BIN=1` before using `command -v simple`.
Their evidence includes `*_simple_bin` and `*_simple_bin_source` fields for
binary provenance.

It runs the generated-GUI Electron matrix, the Simple Web layout manifest,
backend-executed CPU SIMD/Metal parity, and raw Metal framebuffer readback. On
Linux hosts, native Metal readback is recorded as `unavailable` with
`metal-requires-macos`; this is host-unavailable evidence, not a native Metal
pass. The generated-GUI matrix records `text_normalization_pixels` for the
fixture-specific Chrome/Simple text antialiasing normalization and still
requires exact checksums, `mismatch_count=0`, and `blur_or_tolerance=false`.
The wrapper continues independent backend, font offload/readback, and raw Metal
readback checks after an earlier layout or surface failure so one report can
show the first failing gate and later already-proven or still-blocked gates.

### Linux QEMU Network Parity

Use `scripts/qemu/linux_qemu_net_parity_bench.shs` when comparing the same
C/Rust/Simple network parity workload inside a Linux QEMU guest. The harness
requires a caller-supplied bootable guest image with SSH plus benchmark
prerequisites:

```bash
LINUX_QEMU_IMAGE=/path/to/linux.qcow2 \
LINUX_QEMU_SSH_USER=ubuntu \
scripts/qemu/linux_qemu_net_parity_bench.shs
```

Useful knobs include `LINUX_QEMU_DISK=virtio|nvme`,
`LINUX_QEMU_ACCEL=kvm:tcg`, `LINUX_QEMU_SSH_PORT`, `LINUX_QEMU_TIMEOUT`,
`NET_PARITY_ITERS`, and `NET_PARITY_PAYLOAD`.

### Native HTTPServer Static Parity

Use the retained native HTTPServer wrapper when a lane claims Simple static-file
serving is equal to or faster than peer servers:

```bash
sh scripts/check/check-native-pure-simple-goal-status.shs
```

The aggregate status reads retained rows from
`doc/10_metrics/perf/web_server_nginx_compare.md` and the companion report
`doc/09_report/perf/web_server_nginx_compare_2026-06-17.md`. Current retained
static rows are:

| Payload | Simple RPS | Peer | Peer RPS | Status |
|---------|------------|------|----------|--------|
| 1KB | 15503.65 | nginx | 15115.00 | Simple >= peer |
| 1MB | 1884.42 | nginx | 1376.25 | Simple >= peer |

For fresh host-local evidence, use the focused wrappers:

```bash
WRK_DURATION=1s sh scripts/check/check-web-server-nginx-live-compare.shs
WRK_DURATION=1s sh scripts/check/check-web-server-static-external-live-compare.shs --require-simple-ge-all
sh scripts/check/check-web-server-go-erlang-static-compare.shs --require-simple-ge
sh scripts/check/check-httpserver-live-static.shs
sh scripts/check/check-httpserver-static-profile-counters.shs --broad --require-retained
```

The same aggregate status also records the DB B+ gate. For Vulkan offscreen 8K,
`doc/09_report/gpu_db_vulkan_gui_8k_feasibility_2026-06-19.md` records a
host-local RTX A6000 feasibility row of `3527` FPS. Treat that as feasibility
evidence, not a retained release row. Live onscreen 8K remains host-blocked
unless the host provides a suitable display. Do not replace retained rows with
shorter or noisier runs unless the strict wrappers still pass.

---

## Integration with SPipe

### Performance Test

```simple
import std.spec
import std.testing.benchmark as bench

describe "Performance tests":
    it "sorts 1000 items quickly":
        val data = generate_random_list(1000)
        val stats = bench.benchmark_default("sort", \:
            data.clone().sort()
        )
        expect stats.mean_ns < 10_000_000.0  # < 10ms
```

### Regression Detection

```simple
describe "Performance regressions":
    it "maintains O(n log n) complexity":
        val small = bench.benchmark_default("n=1000", \:
            generate_random_list(1000).sort()
        )
        val large = bench.benchmark_default("n=10000", \:
            generate_random_list(10000).sort()
        )
        # Should be ~33x slower for O(n log n), allow 50x margin
        val ratio = large.mean_ns / small.mean_ns
        expect ratio < 50.0
```

---

## Optimization Patterns

### Pattern 1: Reduce Test Data Size

The most effective optimization. 10x data reduction typically yields ~10x speedup.

```simple
# Before (slow -- 10k elements)
slow_it "handles large arrays":
    val elements = [for i in 0..10000: create_element(i)]

# After (fast -- 1k elements, still validates behavior)
slow_it "handles large arrays":
    val elements = [for i in 0..1000: create_element(i)]
```

### Pattern 2: Split Large Test Files

When a test file has 40+ tests and takes 5+ seconds:

```
# Before: single file
literal_converter_spec.spl           # 48 tests, 16s

# After: split by category
literal_converter_basic_spec.spl      # 15 tests, 2s
literal_converter_collections_spec.spl # 18 tests, 3s
literal_converter_perf_spec.spl       #  5 tests, 4s
```

### Pattern 3: Mock External Resources

```simple
# Before (slow -- actual file I/O)
it "reads config":
    file_write("test.conf", "key=value")
    val config = load_config("test.conf")

# After (fast -- in-memory)
it "reads config":
    val mock_fs = MockFileSystem()
    mock_fs.add("test.conf", "key=value")
    val config = load_config_from("test.conf", mock_fs)
```

### Pattern 4: Use Test Data Builders

```simple
fn build_test_array(size: i64) -> Value:
    val elements = [for i in 0..size: Value.Int(i)]
    Value.Array(elements)

it "handles arrays":
    val arr = build_test_array(100)
    expect arr.is_array()
```

### Pattern 5: Before/After Optimization Comparison

```simple
val results = bench.compare_default({
    "old": \: old_implementation(),
    "new": \: new_implementation()
})

val speedup = results["old"].mean_ns / results["new"].mean_ns
print "Speedup: {speedup:.2f}x"
```

### Optimization Workflow

1. **Measure**: `bin/simple test --only-slow` to find slowest tests
2. **Analyze**: Check for large loops, oversized data, missing imports, external I/O
3. **Fix**: Apply quick wins first (reduce data 10x, fix APIs, add mocks)
4. **Verify**: Run specific test and compare timing
5. **Document**: Note patterns and infrastructure created

### Target Metrics

| Category | Target |
|----------|--------|
| Basic tests | < 1 second |
| Integration tests | < 3 seconds |
| Performance tests | < 5 seconds |
| Full suite | < 2 minutes |
| CI pipeline | < 5 minutes |

---

## CI/CD Integration

### GitHub Actions

```yaml
name: Performance Benchmarks
on:
  push:
    branches: [main]

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run benchmarks
        run: simple test benchmarks/
      - name: Check for regressions
        run: simple bench --baseline baseline.json --compare current.json
```

### Tracking Performance Over Time

```simple
val stats = bench.benchmark_default("critical_path", critical_function)
File.write("benchmarks/baseline.json", stats.to_json())

# Later, compare:
val baseline = BenchmarkStats.from_json(File.read("benchmarks/baseline.json"))
val current = bench.benchmark_default("critical_path", critical_function)

if current.mean_ns > baseline.mean_ns * 1.1:
    print "Performance regression detected!"
    exit(1)
```

---

## API Reference

### Functions

| Function | Description | Returns |
|----------|-------------|---------|
| `benchmark(name, func, config)` | Benchmark with custom config | `BenchmarkStats` |
| `benchmark_default(name, func)` | Benchmark with defaults | `BenchmarkStats` |
| `compare(benchmarks, config)` | Compare multiple implementations | `Map<text, BenchmarkStats>` |
| `compare_default(benchmarks)` | Compare with defaults | `Map<text, BenchmarkStats>` |

### Types

**`BenchmarkConfig`** -- Configuration with presets `default()` and `quick()`.

**`BenchmarkStats`** -- Statistical results with `summary()` and `format_time()` methods. Fields: `mean_ns`, `median_ns`, `std_dev_ns`, `min_ns`, `max_ns`, `low_outliers`, `high_outliers`.

---

## Troubleshooting

### High variance (large standard deviation)

1. Increase sample size and warmup iterations
2. Run on idle machine (no background tasks)
3. Disable CPU frequency scaling
4. Check for GC pauses

### Many outliers

1. Increase warmup iterations (prime caches, trigger JIT)
2. Increase sample size
3. Consider using median instead of mean

### Inconsistent results between runs

1. Use longer measurement time
2. Fix system state (disable turbo boost)
3. Use deterministic inputs
4. Avoid I/O or randomness in benchmarks

### Limitations

- Does not show WHERE time is spent (use profiling for that)
- Synthetic workloads may not predict production performance
- Only measures time, not memory usage
- Only tests what you measure
