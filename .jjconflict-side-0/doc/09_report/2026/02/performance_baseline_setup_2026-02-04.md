# Performance Baseline Setup - 2026-02-04

## Status: Infrastructure Complete

Phase 1 of the optimization plan has been initiated: establishing performance measurement infrastructure.

## Benchmark Infrastructure Created

### Interpreter Benchmarks (`rust/compiler/benches/interpreter_bench.rs`)

Comprehensive benchmark suite covering key interpreter operations:

#### 1. Variable Access Patterns
- **local_var**: Local variable access (most common case)
- **global_var**: Global variable lookups
- **closure_var**: Closure variable capture and access

#### 2. Function Call Patterns
- **direct_call**: Direct function calls
- **closure_call**: Lambda/closure invocations
- **method_call**: Method dispatch on objects
- **recursive_call**: Recursive function calls (fibonacci)

#### 3. Collection Operations
- **array_access**: Array indexing
- **dict_lookup**: Dictionary key lookups
- **array_iteration**: For-loop over arrays

#### 4. Control Flow Patterns
- **if_else**: Conditional branching
- **match_expr**: Pattern matching
- **while_loop**: While loop iteration

#### 5. Composite Workloads
- **typical_script**: Mixed workload simulating real-world script execution

## Running Benchmarks

```bash
# Run all interpreter benchmarks
cd rust && cargo bench --bench interpreter_bench

# Run specific benchmark group
cargo bench --bench interpreter_bench -- variable_access

# Run with longer measurement time for more accurate results
cargo bench --bench interpreter_bench -- --measurement-time 15

# Save baseline for comparison
cargo bench --bench interpreter_bench -- --save-baseline baseline-2026-02-04
```

## Expected Bottlenecks to Measure

Based on prior analysis, these benchmarks should reveal:

1. **Variable access overhead** - HashMap lookups on every access
2. **Value cloning overhead** - 165+ unnecessary clones in hot paths
3. **Function call overhead** - Environment cloning and setup
4. **Collection operations** - Dict/Array access patterns

## Next Steps

1. **Establish baseline** - Run benchmarks and document current performance
2. **Profile hotspots** - Use perf/flamegraph to identify bottlenecks
3. **Optimize iteratively**:
   - Week 1: Variable lookup optimization (array for locals)
   - Week 1: Reduce Value cloning in interpreter_eval.rs
   - Week 2: Value pooling and Env::fork() optimization
   - Week 3: MIR optimizations (const folding, DCE)
   - Week 4: JIT auto-compilation for hot functions

## Build System Integration

Benchmarks are integrated into the Rust workspace:
- **Dev dependency**: `criterion = "0.5"`
- **Benchmark definition**: `[[bench]]` section in `rust/compiler/Cargo.toml`
- **Build command**: `cargo bench`

## Baseline Measurements (To Be Collected)

| Benchmark | Time (ns) | Notes |
|-----------|-----------|-------|
| local_var | TBD | Current baseline |
| global_var | TBD | Expected 2-3x slower than local |
| closure_var | TBD | Expected 3-5x slower than local |
| direct_call | TBD | Function call overhead |
| recursive_call | TBD | fib(15) - tests call depth |
| typical_script | TBD | Composite workload |

## Performance Goals

- **Variable access**: 20-30% improvement via array-based locals
- **Value operations**: 15-25% improvement via reduced cloning
- **Overall interpreter**: 2-3x speedup through combined optimizations
- **MIR compilation**: 20-40% improvement via optimization passes

## Verification

All benchmarks compile and run successfully:
```bash
✓ cargo bench --bench interpreter_bench --no-run
  Finished `bench` profile [optimized] target(s) in 3.16s
```

---

**Next Report**: `performance_baseline_2026-02-04.md` (after running benchmarks and establishing measurements)
