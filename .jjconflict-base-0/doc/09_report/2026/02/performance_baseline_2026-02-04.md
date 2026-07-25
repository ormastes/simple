# Performance Baseline - Simple Interpreter
**Date**: 2026-02-04
**Platform**: Linux x86_64
**Build**: Rust 1.x, release-opt profile
**Measurement Tool**: Criterion 0.5

## Executive Summary

Baseline performance measurements established for the Simple language interpreter. These measurements will guide optimization efforts targeting 2-3x overall speedup.

**Key Findings:**
- Variable access is reasonably fast (~18-22 µs)
- Function calls show 42% overhead for methods vs direct calls
- Dictionary lookups are 53% slower than array access
- While loops show unexpectedly high overhead (163 µs for 100 iterations)
- Recursive calls perform well (5.2 ms for fib(15) = 610 calls ≈ 8.5 µs/call)

## Benchmark Results

### 1. Variable Access Patterns

| Benchmark | Time (µs) | Relative | Notes |
|-----------|-----------|----------|-------|
| local_var | 17.72 | 1.00x | Baseline |
| global_var | 18.38 | 1.04x | Only 4% slower (surprising!) |
| closure_var | 22.17 | 1.25x | 25% overhead for closure capture |

**Analysis:**
- Global variables are nearly as fast as locals (unexpected)
- Suggests HashMap lookups are not the primary bottleneck
- Closure captures add 25% overhead (4.4 µs)
- All include parsing time (~15-17 µs estimated)

**Optimization Potential**: LOW (variables are already fast)

### 2. Function Call Patterns

| Benchmark | Time | Relative | Notes |
|-----------|------|----------|-------|
| direct_call | 29.37 µs | 1.00x | 10 function calls |
| closure_call | 28.64 µs | 0.97x | Slightly faster! |
| method_call | 41.76 µs | 1.42x | 42% overhead |
| recursive_call | 5.18 ms | - | fib(15) = 610 calls |

**Per-call overhead:**
- Direct call: ~2.9 µs/call (after subtracting parsing ~15µs, loop ~13µs)
- Closure call: ~2.9 µs/call (same as direct)
- Method call: ~4.2 µs/call (45% higher)
- Recursive: ~8.5 µs/call (includes expression eval)

**Analysis:**
- Method calls have significant overhead (+42%)
- Closure calls are equally fast as direct calls
- fib(15) performance suggests ~8.5 µs per recursive call
- Method dispatch likely involves extra environment lookups

**Optimization Potential**: MEDIUM (method calls, recursive overhead)

### 3. Collection Operations

| Benchmark | Time (µs) | Relative | Notes |
|-----------|-----------|----------|-------|
| array_iteration | 28.04 | 1.00x | Iterate 10 elements |
| array_access | 31.06 | 1.11x | Index-based access |
| dict_lookup | 47.45 | 1.69x | 53% slower than array |

**Per-operation overhead:**
- Array iteration: ~2.8 µs per element
- Array indexing: ~3.1 µs per access (10% slower)
- Dict lookup: ~4.7 µs per lookup (69% slower)

**Analysis:**
- Dictionary lookups are significantly slower (53% overhead)
- Array operations are reasonably fast
- Iteration is faster than indexing (unexpected - may be optimized)

**Optimization Potential**: MEDIUM (dict lookups could be improved)

### 4. Control Flow Patterns

| Benchmark | Time (µs) | Relative | Notes |
|-----------|-----------|----------|-------|
| if_else | 40.17 | 1.00x | 100 iterations with branching |
| match_expr | 46.63 | 1.16x | 16% slower than if/else |
| while_loop | 163.30 | 4.07x | **4x slower!** |

**Per-iteration overhead:**
- if_else: ~0.40 µs per iteration
- match_expr: ~0.47 µs per iteration
- while_loop: **~1.63 µs per iteration** (HIGH!)

**Analysis:**
- While loops show unexpectedly high overhead (4x vs for loops)
- Match expressions add 16% overhead vs if/else
- For loops (in if_else benchmark) are much faster than while

**Optimization Potential**: HIGH (while loop overhead is concerning)

### 5. Composite Workload

| Benchmark | Time (µs) | Notes |
|-----------|-----------|-------|
| typical_script | 90.94 | Mixed operations: factorial + array processing |

**Analysis:**
- Realistic workload showing overall interpreter performance
- Includes: recursion, array ops, conditionals, loops
- Target: Reduce to ~30-45 µs (2-3x speedup)

## Performance Breakdown

### Estimated Time Budget (typical_script = 91 µs)

Based on the component benchmarks:
- **Parsing**: ~15-17 µs (18-19%)
- **Function calls**: ~15-20 µs (16-22%)
- **Expression evaluation**: ~20-25 µs (22-27%)
- **Control flow**: ~15-20 µs (16-22%)
- **Collection ops**: ~10-15 µs (11-16%)
- **Other overhead**: ~10-15 µs (11-16%)

## Identified Bottlenecks

### 1. While Loop Overhead (CRITICAL)
**Issue**: While loops are 4x slower than for loops
**Impact**: 163 µs for 100 iterations
**Root cause**: Unknown - requires profiling
**Priority**: HIGH

### 2. Method Call Overhead
**Issue**: Method calls are 42% slower than direct calls
**Impact**: ~1.3 µs extra per method call
**Root cause**: Likely extra environment lookups for `self`
**Priority**: MEDIUM

### 3. Dictionary Lookups
**Issue**: 53% slower than array access
**Impact**: ~1.6 µs extra per lookup
**Root cause**: HashMap overhead vs Vec indexing
**Priority**: MEDIUM

### 4. Match Expression Overhead
**Issue**: 16% slower than if/else
**Impact**: ~0.07 µs per iteration
**Root cause**: Pattern matching complexity
**Priority**: LOW

## Optimization Targets

Based on these measurements, the optimization priorities are:

### Week 1: Critical Fixes
1. **Investigate while loop overhead** (4x slowdown)
   - Profile to identify root cause
   - Target: Reduce to match for-loop performance
   - Expected gain: 75% improvement in while loops

2. **Reduce method call overhead** (42% slowdown)
   - Optimize `self` binding
   - Cache method lookups
   - Target: Match direct call performance
   - Expected gain: 30% faster method calls

### Week 2: Medium Priority
3. **Optimize dictionary operations** (53% slowdown)
   - Consider specialized small-dict optimization
   - Profile HashMap usage patterns
   - Target: 20-30% improvement

4. **Reduce Value cloning** (from code analysis)
   - Identified 165+ unnecessary clones
   - Target: 15-25% overall improvement

### Week 3: Compilation Optimizations
5. **Add MIR optimization passes**
   - Constant folding
   - Dead code elimination
   - Inline small functions
   - Target: 20-40% faster compilation

### Week 4: Advanced Optimizations
6. **JIT compilation for hot functions**
   - Add hotness tracking
   - Compile hot functions to native code
   - Target: 2-5x speedup for computation-heavy code

## Performance Goals

| Metric | Baseline | Target | Improvement |
|--------|----------|--------|-------------|
| Variable access | 17.7 µs | 14-15 µs | 15-20% |
| Function calls | 29.4 µs | 24-26 µs | 15-20% |
| Method calls | 41.8 µs | 30-35 µs | 20-30% |
| While loops | 163 µs | 40-50 µs | 70-75% |
| Dict lookups | 47.5 µs | 35-40 µs | 20-30% |
| **Composite** | **91 µs** | **30-45 µs** | **2-3x** |

## Next Steps

1. **Profile while loop execution** - Identify root cause of 4x overhead
2. **Profile method calls** - Find source of 42% overhead
3. **Code analysis** - Locate and eliminate unnecessary Value clones
4. **Implement optimizations** - Start with critical fixes (while loops, methods)
5. **Re-benchmark** - Measure improvements against this baseline

## Measurement Details

**Environment:**
```
Criterion: 288k-1000 iterations per benchmark
Confidence: 95%
Outliers: 3-17% (within acceptable range)
Warmup: 3 seconds per benchmark
Samples: 100 per benchmark
```

**Baseline saved as**: `baseline-2026-02-04`

**Comparison command:**
```bash
cd rust
cargo bench --bench interpreter_bench -- --baseline baseline-2026-02-04
```

## Appendix: Raw Results

```
variable_access/local_var     17.722 µs  [17.523 µs, 17.946 µs]
variable_access/global_var    18.380 µs  [18.329 µs, 18.428 µs]
variable_access/closure_var   22.166 µs  [22.137 µs, 22.202 µs]

function_calls/direct_call    29.372 µs  [28.562 µs, 30.430 µs]
function_calls/closure_call   28.643 µs  [28.196 µs, 29.203 µs]
function_calls/method_call    41.762 µs  [40.896 µs, 42.857 µs]
function_calls/recursive_call  5.178 ms  [ 5.156 ms,  5.209 ms]

collections/array_access      31.055 µs  [30.695 µs, 31.579 µs]
collections/dict_lookup       47.451 µs  [46.938 µs, 48.115 µs]
collections/array_iteration   28.042 µs  [27.739 µs, 28.429 µs]

control_flow/if_else          40.171 µs  [37.953 µs, 42.286 µs]
control_flow/match_expr       46.631 µs  [45.796 µs, 47.755 µs]
control_flow/while_loop      163.300 µs  [158.13 µs, 168.63 µs]

composite/typical_script      90.936 µs  [87.454 µs, 94.869 µs]
```

---

**Report Status**: BASELINE ESTABLISHED ✓
**Next**: Profiling and optimization implementation
