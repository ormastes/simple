# Interpreter Profiling Tools

Tools for profiling and analyzing Simple interpreter performance.

## Prerequisites

### Linux (Ubuntu/Debian)
```bash
# Install perf
sudo apt-get install linux-tools-generic linux-tools-$(uname -r)

# Install flamegraph
cargo install flamegraph

# Enable perf for non-root users (optional)
sudo sysctl -w kernel.perf_event_paranoid=1
```

### macOS
```bash
# macOS uses Instruments instead of perf
# Install Xcode Command Line Tools
xcode-select --install

# Flamegraph still works with DTrace
cargo install flamegraph
```

## Quick Start

### 1. Run Benchmarks
```bash
# Run all benchmarks and save baseline
cd rust && cargo bench --bench interpreter_bench -- --save-baseline baseline-2026-02-04

# Run specific benchmark group
cargo bench --bench interpreter_bench -- variable_access

# Compare with baseline
cargo bench --bench interpreter_bench -- --baseline baseline-2026-02-04
```

### 2. Profile a Script
```bash
# Profile any Simple script
./script/profiling/profile-interpreter.sh examples/fibonacci.spl

# Profile with custom settings
./script/profiling/profile-interpreter.sh test.spl --freq=999 --time=20

# Profile benchmark workload
./script/profiling/profile-interpreter.sh --benchmark --time=30
```

**Output**: `flamegraph.svg` - Interactive visualization of CPU time

### 3. Analyze Hotspots
```bash
# After profiling, analyze the results
./script/profiling/analyze-hotspots.sh perf.data

# Interactive exploration
perf report -i perf.data

# Annotated source code
perf annotate -i perf.data
```

## Profiling Workflow

### Step 1: Establish Baseline
```bash
# Run benchmarks and record baseline
cd rust
cargo bench --bench interpreter_bench -- --save-baseline before-optimization

# Profile a representative workload
cd ..
./script/profiling/profile-interpreter.sh --benchmark --output=before.svg
```

### Step 2: Identify Bottlenecks
```bash
# Analyze hotspots
./script/profiling/analyze-hotspots.sh

# Look for:
# - Functions with high CPU overhead (>5%)
# - Deep call stacks
# - Excessive cloning or allocation
# - HashMap lookups in hot paths
```

### Step 3: Optimize
Based on the analysis, implement optimizations:
- Variable lookup optimization (array for locals)
- Reduce Value cloning
- Optimize Env::fork()
- Add value pooling

### Step 4: Measure Improvement
```bash
# Run benchmarks and compare
cd rust
cargo bench --bench interpreter_bench -- --baseline before-optimization

# Profile optimized version
cd ..
./script/profiling/profile-interpreter.sh --benchmark --output=after.svg

# Compare flamegraphs visually
firefox before.svg after.svg
```

## Understanding Flamegraphs

### Reading the Visualization
- **Width**: Proportion of CPU time
- **Height**: Call stack depth (not duration!)
- **Color**: Random (for visual distinction only)

### What to Look For
1. **Wide plateaus** - Functions consuming significant CPU time
2. **Towers** - Deep call stacks (potential for inlining)
3. **Repetitive patterns** - Opportunities for caching

### Common Interpreter Hotspots
- `interpreter_eval::eval_*` - Expression evaluation
- `interpreter_call::exec_function` - Function calls
- `Env::get` / `Env::insert` - Variable lookups
- `Value::clone` - Value copying
- `HashMap::get` / `HashMap::insert` - Environment lookups

## Performance Targets

Based on initial analysis, expected improvements:

| Optimization | Target | Technique |
|--------------|--------|-----------|
| Variable access | 20-30% | Array for locals |
| Value operations | 15-25% | Reduce cloning |
| Function calls | 10-15% | Optimize Env::fork() |
| Overall interpreter | 2-3x | Combined optimizations |

## Benchmark Results Format

Criterion outputs results in microseconds (µs):
```
variable_access/local_var
                        time:   [17.523 µs 17.722 µs 17.946 µs]
                                 ^^^^^^^^  ^^^^^^^^  ^^^^^^^^
                                 lower     estimate  upper
                                 bound                bound
```

**Interpreting results**:
- Estimate: Most likely performance
- Bounds: 95% confidence interval
- Outliers: Measurements outside normal distribution

## Troubleshooting

### "perf: Permission denied"
```bash
# Option 1: Run with sudo
sudo ./script/profiling/profile-interpreter.sh script.spl

# Option 2: Lower paranoid level
sudo sysctl -w kernel.perf_event_paranoid=1
```

### "No such file or directory: perf"
```bash
# Install perf for your kernel version
sudo apt-get install linux-tools-$(uname -r)
```

### "Gnuplot not found"
This is harmless - Criterion will use plotters backend instead.
```bash
# Optional: Install gnuplot for nicer graphs
sudo apt-get install gnuplot
```

## Advanced Profiling

### Cache Misses
```bash
# Profile cache performance
perf stat -e cache-references,cache-misses,cycles,instructions \
  rust/target/release/simple script.spl
```

### Branch Prediction
```bash
# Profile branch mispredictions
perf stat -e branches,branch-misses \
  rust/target/release/simple script.spl
```

### Memory Allocation
```bash
# Profile with Valgrind (slower but detailed)
valgrind --tool=massif rust/target/release/simple script.spl
ms_print massif.out.*
```

## References

- [Criterion.rs Documentation](https://bheisler.github.io/criterion.rs/book/)
- [Linux perf Examples](https://www.brendangregg.com/perf.html)
- [Flamegraph Guide](https://www.brendangregg.com/flamegraphs.html)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
