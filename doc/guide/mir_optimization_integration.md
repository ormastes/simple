# MIR Optimization Framework - Integration Guide

**Status:** Implementation Complete, Integration Pending
**Version:** 1.0.0
**Date:** 2026-02-03

---

## Overview

This guide explains how to integrate the MIR optimization framework into the Simple compiler pipeline.

**What's Complete:**
- ✅ 7 optimization passes implemented
- ✅ Pass trait system and pipeline
- ✅ 4 optimization levels configured
- ✅ 40+ test cases written

**What's Needed:**
- ⏳ Wire into compilation pipeline
- ⏳ Add CLI flags
- ⏳ Run tests and verify correctness
- ⏳ Measure performance

---

## Quick Start

### 1. Import the Framework

```simple
# In src/compiler/pipeline.spl (or equivalent)

use compiler.mir_opt.mod.{OptLevel, OptimizationPipeline}
```

### 2. Add Optimization Step

```simple
fn compile_module(hir_module: HirModule, opt_level: OptLevel) -> Result<CompiledModule, Error>:
    # Step 1: Lower HIR to MIR
    val mir_module = hir_to_mir(hir_module)?

    # Step 2: Optimize MIR (NEW!)
    val optimized_mir = optimize_mir(mir_module, opt_level)?

    # Step 3: Generate native code
    val compiled = mir_to_native(optimized_mir)?

    Ok(compiled)

fn optimize_mir(mir: MirModule, level: OptLevel) -> Result<MirModule, Error>:
    """Apply MIR optimizations according to optimization level."""
    val pipeline = OptimizationPipeline.for_level(level)
    val optimized = pipeline.optimize(mir)
    Ok(optimized)
```

### 3. Add CLI Support

```simple
# In src/app/cli/main.spl (or equivalent)

enum OptLevelArg:
    None
    Size
    Speed
    Aggressive

fn parse_opt_level(arg: text) -> OptLevelArg:
    match arg:
        "none": OptLevelArg.None
        "size": OptLevelArg.Size
        "speed": OptLevelArg.Speed
        "aggressive": OptLevelArg.Aggressive
        _: OptLevelArg.Speed  # Default to speed

# Usage:
# simple build --opt-level=speed
# simple build --opt-level=aggressive
```

---

## Detailed Integration Steps

### Step 1: Locate Compilation Pipeline

Find the main compilation entry point. This is typically in one of these files:

- `src/compiler/pipeline.spl`
- `src/compiler/compile.spl`
- `src/compiler/driver.spl`
- `src/app/build/compile.spl`

Look for a function that:
1. Takes HIR (High-level IR) as input
2. Produces compiled output (native code)
3. Has steps like: parse → typecheck → lower → codegen

### Step 2: Add MIR Optimization Hook

Insert the optimization step **after MIR lowering** and **before codegen**:

```simple
# BEFORE:
fn compile(source: text, opts: CompileOptions) -> CompiledOutput:
    val ast = parse(source)?
    val hir = ast_to_hir(ast)?
    val mir = hir_to_mir(hir)?
    val output = mir_to_native(mir)?  # <- Add optimization before this
    Ok(output)

# AFTER:
fn compile(source: text, opts: CompileOptions) -> CompiledOutput:
    val ast = parse(source)?
    val hir = ast_to_hir(ast)?
    val mir = hir_to_mir(hir)?

    # NEW: Apply optimizations
    val optimized_mir = if opts.optimize:
        optimize_mir(mir, opts.opt_level)?
    else:
        mir  # No optimization

    val output = mir_to_native(optimized_mir)?
    Ok(output)
```

### Step 3: Add Optimization Options

Add optimization flags to your `CompileOptions` struct:

```simple
struct CompileOptions:
    optimize: bool           # Enable/disable optimization
    opt_level: OptLevel      # Optimization level
    show_stats: bool         # Show optimization statistics
    # ... other options

impl CompileOptions:
    static fn debug() -> CompileOptions:
        """Debug build (no optimization)."""
        CompileOptions(
            optimize: false,
            opt_level: OptLevel.None,
            show_stats: false
        )

    static fn release() -> CompileOptions:
        """Release build (speed optimization)."""
        CompileOptions(
            optimize: true,
            opt_level: OptLevel.Speed,
            show_stats: false
        )

    static fn release_size() -> CompileOptions:
        """Release build optimized for size."""
        CompileOptions(
            optimize: true,
            opt_level: OptLevel.Size,
            show_stats: false
        )
```

### Step 4: Update CLI Argument Parsing

Add command-line flags for optimization:

```simple
# In CLI parser (src/app/cli/main.spl or equivalent)

fn parse_args(args: [text]) -> CompileOptions:
    var opts = CompileOptions.debug()  # Default

    for arg in args:
        if arg.starts_with("--opt-level="):
            val level_str = arg.split("=")[1]
            opts.opt_level = parse_opt_level(level_str)
            opts.optimize = true

        elif arg == "-O0":
            opts.opt_level = OptLevel.None
            opts.optimize = false

        elif arg == "-O1" or arg == "-Os":
            opts.opt_level = OptLevel.Size
            opts.optimize = true

        elif arg == "-O2":
            opts.opt_level = OptLevel.Speed
            opts.optimize = true

        elif arg == "-O3":
            opts.opt_level = OptLevel.Aggressive
            opts.optimize = true

        elif arg == "--show-opt-stats":
            opts.show_stats = true

    opts
```

### Step 5: Display Statistics (Optional)

Show optimization statistics when requested:

```simple
fn optimize_mir(mir: MirModule, level: OptLevel, show_stats: bool) -> MirModule:
    val pipeline = OptimizationPipeline.for_level(level)
    val optimized = pipeline.optimize(mir)

    if show_stats:
        print_optimization_stats(pipeline)

    optimized

fn print_optimization_stats(pipeline: OptimizationPipeline):
    """Display optimization statistics."""
    print "Optimization Statistics:"
    print "  Level: {pipeline.level}"
    print "  Passes: {pipeline.passes.len()}"

    # Get stats from each pass (if tracking enabled)
    for pass_name in pipeline.passes:
        # TODO: Fetch and display per-pass statistics
        print "  {pass_name}: [stats here]"
```

---

## CLI Usage Examples

Once integrated, users can compile with different optimization levels:

```bash
# No optimization (fastest compile, slowest runtime)
simple build --opt-level=none
simple build -O0

# Size optimization (smaller binaries)
simple build --opt-level=size
simple build -Os

# Speed optimization (default release)
simple build --opt-level=speed
simple build -O2

# Aggressive optimization (maximum performance)
simple build --opt-level=aggressive
simple build -O3

# Show optimization statistics
simple build -O2 --show-opt-stats

# Debug build (alias for --opt-level=none)
simple build

# Release build (alias for --opt-level=speed)
simple build --release
```

---

## Testing the Integration

### 1. Smoke Tests

Create simple test programs to verify basic functionality:

**test_constant_folding.spl:**
```simple
fn main():
    val x = 2 + 3  # Should fold to 5
    print x
```

Compile and verify:
```bash
simple build test_constant_folding.spl -O2
./test_constant_folding  # Should print 5
```

**test_dead_code.spl:**
```simple
fn main():
    val unused = expensive_function()  # Should be eliminated
    print "Hello"
```

Compile and check that `expensive_function` is not called (check generated code or profile).

### 2. Correctness Tests

Run existing test suite with optimization enabled:

```bash
# Run tests with optimization
simple test --opt-level=speed

# Compare with unoptimized
simple test --opt-level=none

# Results should be identical (correctness preserved)
```

### 3. Performance Benchmarks

Create benchmarks to measure optimization impact:

**bench_loop.spl:**
```simple
fn fibonacci(n: i64) -> i64:
    if n <= 1:
        return n
    return fibonacci(n - 1) + fibonacci(n - 2)

fn main():
    val start = time.now()
    val result = fibonacci(30)
    val end = time.now()
    print "Result: {result}"
    print "Time: {end - start}ms"
```

Compare performance:
```bash
# Unoptimized
simple build bench_loop.spl -O0
./bench_loop  # Record time

# Optimized
simple build bench_loop.spl -O2
./bench_loop  # Should be faster

# Aggressive
simple build bench_loop.spl -O3
./bench_loop  # Should be fastest
```

### 4. Binary Size Comparison

Measure binary sizes:
```bash
# Size optimization
simple build large_program.spl -Os
ls -lh large_program  # Smallest

# Speed optimization
simple build large_program.spl -O2
ls -lh large_program  # Medium

# Aggressive
simple build large_program.spl -O3
ls -lh large_program  # Largest (due to inlining/unrolling)
```

---

## Expected Performance Impact

### Compile-Time Overhead

| Optimization Level | Additional Time | Example (1000 LOC) |
|-------------------|----------------|-------------------|
| None (baseline) | +0% | 100ms |
| Size | +12-18% | 112-118ms |
| Speed | +15-25% | 115-125ms |
| Aggressive | +25-40% | 125-140ms |

**Note:** Overhead is proportional to code size. Small programs see minimal impact.

### Runtime Performance

| Workload Type | Size | Speed | Aggressive |
|--------------|------|-------|-----------|
| Math-heavy | +5-10% | +10-18% | +15-25% |
| Function-heavy | +8-15% | +20-30% | +28-40% |
| Loop-heavy | +10-15% | +25-35% | +35-50% |
| Mixed | +7-12% | +15-25% | +25-40% |

**Note:** Actual results depend heavily on code characteristics.

### Binary Size

| Optimization Level | Size Impact | Reason |
|-------------------|-------------|--------|
| None | Baseline (100%) | No optimization |
| Size | -10-20% | DCE + minimal inlining |
| Speed | -5-10% | DCE + moderate inlining |
| Aggressive | +5-10% | Heavy inlining + unrolling |

---

## Troubleshooting

### Problem: Optimization Makes Code Slower

**Symptoms:**
- Optimized code runs slower than unoptimized
- `-O3` slower than `-O2`

**Possible Causes:**
1. **I-cache thrashing** from excessive inlining/unrolling
2. **Register spilling** from too many local variables
3. **Poor branch prediction** from complex control flow

**Solutions:**
- Try `-O2` instead of `-O3`
- Reduce inlining threshold
- Profile to find hot spots
- Use `--show-opt-stats` to see what optimizations applied

### Problem: Optimized Code Produces Wrong Results

**Symptoms:**
- Test failures with optimization enabled
- Different output with `-O2` vs `-O0`

**This is a BUG!** Optimization must preserve semantics.

**Debug Steps:**
1. Isolate the failing test case
2. Try different optimization levels to narrow down which pass causes the issue
3. Check if it's a DCE problem (side effect not preserved)
4. Check if it's a CSE problem (incorrect invalidation)
5. File a bug report with minimal reproducing example

### Problem: Compilation Crashes with Optimization

**Symptoms:**
- Compiler crashes during optimization
- Stack overflow or out of memory

**Debug Steps:**
1. Try with `--opt-level=none` - if it works, it's an optimization bug
2. Try each pass individually to isolate the problematic pass
3. Check for infinite loops in pass logic (e.g., cycle detection)
4. Check for stack overflow in recursive algorithms
5. File a bug report

---

## Pass Configuration (Advanced)

For advanced users, you can customize which passes run:

```simple
# Custom optimization pipeline
fn create_custom_pipeline() -> OptimizationPipeline:
    OptimizationPipeline(
        level: OptLevel.Speed,
        passes: [
            "dead_code_elimination",
            "constant_folding",
            "copy_propagation",
            # Skip CSE for faster compile
            "inline_functions",
            "dead_code_elimination"  # Cleanup
        ]
    )
```

CLI support for custom passes (optional feature):
```bash
simple build --passes="dce,const_fold,copy_prop" myprogram.spl
```

---

## Performance Tuning

### Tuning Inlining

Adjust inlining thresholds for your workload:

```simple
# In src/compiler/mir_opt/inline.spl

# For embedded (minimize code size)
val conservative_inline = FunctionInlining.new(
    threshold: 30,  # Even smaller than default 50
    policy: InlinePolicy.Conservative
)

# For server (maximize speed, code size ok)
val aggressive_inline = FunctionInlining.new(
    threshold: 5000,  # Much larger than default 2000
    policy: InlinePolicy.Aggressive
)
```

### Tuning Loop Unrolling

Adjust unrolling threshold:

```simple
# In src/compiler/mir_opt/loop_opt.spl

# Conservative (code size focus)
val conservative_unroll = LoopUnroller.new(threshold: 2)

# Aggressive (performance focus)
val aggressive_unroll = LoopUnroller.new(threshold: 16)
```

---

## Next Steps

1. **Integrate into pipeline** - Add optimization hook to compiler
2. **Add CLI flags** - Enable user control of optimization level
3. **Run tests** - Verify correctness with optimization enabled
4. **Measure performance** - Create benchmarks and collect data
5. **Tune thresholds** - Adjust based on real-world results
6. **Document findings** - Update this guide with actual performance numbers

---

## References

**Implementation:**
- `src/compiler/mir_opt/mod.spl` - Framework and pipeline
- `src/compiler/mir_opt/*.spl` - Individual passes

**Tests:**
- `test/compiler/mir_opt_spec.spl` - 40+ unit tests

**Documentation:**
- `doc/report/mir_optimization_complete_2026-02-03.md` - Implementation report
- `doc/report/compiler_features_session_complete_2026-02-03.md` - Session summary

---

## Support

If you encounter issues integrating the optimization framework:

1. Check that all imports are correct
2. Verify `OptLevel` enum is accessible from your code
3. Run the test suite to ensure passes work correctly
4. Check compiler logs for optimization-related errors
5. Use `--show-opt-stats` to debug which passes are running

For bugs or feature requests, file an issue with:
- Minimal reproducing example
- Optimization level used
- Expected vs actual behavior
- Compiler version and commit hash

---

**Last Updated:** 2026-02-03
**Status:** Ready for Integration
**Author:** Claude (Sonnet 4.5)
