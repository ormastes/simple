---
name: benchmark
description: Performance benchmarking, profiling, regression testing for compiler and runtime
---

# Performance Benchmarking

## Quick Commands

```bash
bin/simple build --release --profile  # Release build with profiling
bin/simple test --only-slow           # Run performance-sensitive tests
```

## Compiler Benchmarks

### Build Time
```bash
time bin/simple build                 # Debug build time
time bin/simple build --release       # Release build time
```

### Bootstrap Time
```bash
time bin/simple build bootstrap       # Full bootstrap cycle
```

## Runtime Benchmarks

### Interpreter Performance
- Use the `--profile` flag for built-in performance measurement
- Clock primitives and perf probes available in stdlib

### Memory Usage
- Monitor RSS during test suite execution
- Track peak memory during compilation phases

## Profiling Tools

### Built-in Profiling
```bash
bin/simple build --profile            # Enable perf probes
```

### External Tools
```bash
perf record bin/simple build          # Linux perf
perf report
```

## Regression Testing

### Before/After Comparison
1. Record baseline: `time bin/simple test > baseline.log 2>&1`
2. Make changes
3. Record new: `time bin/simple test > after.log 2>&1`
4. Compare timing differences

### Key Metrics
- Total test suite time
- Bootstrap cycle time
- Release build time
- Peak memory usage

## Performance Rules

- **Never regress bootstrap time** without justification
- **Profile before optimizing** — measure, don't guess
- **Benchmark release builds** — debug builds have different characteristics
- **Test on representative workloads** — microbenchmarks can mislead
