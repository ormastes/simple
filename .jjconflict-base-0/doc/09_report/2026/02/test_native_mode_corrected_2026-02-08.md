# Test Native Mode - CORRECTED Analysis - 2026-02-08

## 🔴 CORRECTION: Native Compilation EXISTS

**Previous incorrect statement:** "Native mode is not fully implemented"
**CORRECT:** Native compilation fully exists with JIT and AOT modes

## Compilation Modes Available

From `src/compiler/driver_types.spl`:

```simple
enum CompileMode:
    Interpret       # Tree-walking interpreter (default for tests)
    Jit             # JIT compile and run via Cranelift
    Aot             # Ahead-of-time compile to executable
    Check           # Type check only, no execution
    Sdn             # SDN data parsing mode
```

## Native Compilation Architecture

### Components

**Location:** `src/compiler/`

| Component | File | Purpose |
|-----------|------|---------|
| **Driver** | `driver.spl` | Main compiler orchestration |
| **Codegen** | `codegen.spl` | Native code generation via Cranelift FFI |
| **JIT Context** | `loader/jit_context.spl` | JIT compilation context |
| **Build Native** | `build_native.spl` | Build pipeline for native binaries |
| **Linker** | `linker/` | Simple linker (mold-based) |
| **Loader** | `loader/` | Module loader with JIT instantiation |

### Compilation Pipeline

**JIT Mode** (`CompileMode.Jit`):
```
Source → Parse → HIR → Type Check → MIR → Optimize → JIT Compile → Execute
```

**AOT Mode** (`CompileMode.Aot`):
```
Source → Parse → HIR → Type Check → MIR → Optimize → Native Binary
```

**Implementation:** `src/compiler/driver.spl`
- Line 117-119: JIT mode → `jit_compile_and_run()`
- Line 121-123: AOT mode → `aot_compile()`

### Backend: Cranelift via FFI

**Codegen:** `src/compiler/codegen.spl`

```simple
struct Codegen:
    module_handle: i64
    current_ctx: i64
    target: CodegenTarget      # X86_64, Aarch64, Riscv64, Native
    mode: CodegenMode          # Jit or Aot
    local_values: Dict<i64, i64>
    function_map: Dict<text, i64>
    errors: [CodegenError]
```

**Targets Supported:**
- x86_64 (default)
- aarch64
- riscv64

**FFI Functions:** (via `ffi.codegen*`)
- `cranelift_new_module()` - Create JIT module
- `cranelift_new_aot_module()` - Create AOT module
- `cranelift_begin_function()` - Start function compilation
- `cranelift_finalize_module()` - Finalize module
- `cranelift_free_module()` - Free resources

## Why Test Runner Shows "Native mode not supported"

### The Issue

**Test runner implementation:** `src/app/test_runner_new/test_runner_execute.spl`

Lines 357-373: `run_test_file_native()`:
```simple
fn run_test_file_native(file_path: text, options: TestOptions) -> TestFileResult:
    val binary = find_simple_binary()
    # ...
    var run_args: [text] = [file_path]  # ← Just passes file to interpreter!
    # ...
    val (stdout, stderr, exit_code) = process_run_timeout(binary, run_args, timeout_ms)
```

**Problem:** The "native" mode in test runner just runs the file through the interpreter - it doesn't actually invoke JIT/AOT compilation!

### What Should Happen

**Correct native test execution:**

1. **Compile test file with JIT:**
   ```bash
   simple --mode=jit test_file_spec.spl
   ```

2. **Or compile with AOT:**
   ```bash
   simple compile test_file_spec.spl -o test_binary
   ./test_binary
   ```

3. **Test runner should invoke compiler:**
   ```simple
   fn run_test_file_native(file_path: text, options: TestOptions) -> TestFileResult:
       # Option 1: Use JIT mode
       val result = compiler_driver.compile_with_mode(file_path, CompileMode.Jit)

       # Option 2: Compile to binary and execute
       val binary = compile_to_native(file_path)
       process_run(binary, [])
   ```

## How to Actually Use Native Compilation

### Via CLI

**JIT Compile and Run:**
```bash
# Run file with JIT compilation
simple --mode=jit myprogram.spl

# Or use short form
simple -j myprogram.spl
```

**AOT Compile to Binary:**
```bash
# Compile to executable
simple compile myprogram.spl -o myprogram

# Run the binary
./myprogram
```

**Build Native Binary (Full Pipeline):**
```bash
# Build with Simple linker
simple build --release

# This uses src/compiler/build_native.spl:
# 1. Compile source files to SMF
# 2. Link SMFs using Simple linker
# 3. Generate native binary via mold
```

### Via API

**From Simple Code:**
```simple
use compiler.driver.*
use compiler.driver_types.*

# Create compiler with JIT mode
val options = CompileOptions(
    input_files: ["myprogram.spl"],
    mode: CompileMode.Jit,
    optimization_level: 2
)

val driver = CompilerDriver.create(options)
val result = driver.compile()

match result:
    case CompileResult.Success(_):
        print "JIT compilation succeeded!"
    case CompileResult.CodegenError(errors):
        print "Codegen failed: {errors}"
```

## How to Fix Test Runner for True Native Mode

### Implementation Plan

**File:** `src/app/test_runner_new/test_runner_execute.spl`

**Option 1: Use Compiler API (Recommended)**
```simple
fn run_test_file_native(file_path: text, options: TestOptions) -> TestFileResult:
    use compiler.driver.*
    use compiler.driver_types.*

    val start = time_now_unix_micros()

    # Create compiler options for JIT mode
    val compile_opts = CompileOptions(
        input_files: [file_path],
        mode: CompileMode.Jit,
        optimization_level: 2,
        verbose: options.verbose
    )

    # Compile and run with JIT
    val driver = CompilerDriver.create(compile_opts)
    val result = driver.compile()

    val end = time_now_unix_micros()
    val duration_ms = (end - start) / 1000

    match result:
        case CompileResult.Success(_):
            # JIT execution completed successfully
            make_result_from_jit(file_path, result, duration_ms)
        case CompileResult.CodegenError(errors):
            TestFileResult(
                path: file_path,
                passed: 0,
                failed: 1,
                error: errors.join("; "),
                duration_ms: duration_ms
            )
```

**Option 2: Shell Out to Compiler (Simpler)**
```simple
fn run_test_file_native(file_path: text, options: TestOptions) -> TestFileResult:
    val binary = find_simple_binary()
    val start = time_now_unix_micros()

    # Run with JIT mode
    var args: [text] = ["--mode=jit", file_path]
    if options.gc_log:
        args.push("--gc-log")

    val (stdout, stderr, exit_code) = process_run_timeout(binary, args, timeout_ms)
    val duration_ms = (time_now_unix_micros() - start) / 1000

    make_result_from_output(file_path, stdout, stderr, exit_code, duration_ms, options.timeout)
```

## Current Test Execution Modes

### What Actually Works

**Interpreter Mode** (default): `--mode=interpreter`
- Tree-walking interpreter
- No compilation
- Slowest but most compatible

**SMF Mode**: `--mode=smf`
- Uses precompiled `.smf` bytecode if available
- Falls back to interpreter if no `.smf`

**Safe Mode**: `--safe-mode`
- Interpreter with resource limits
- Memory: 512 MB
- CPU: 30 seconds
- File descriptors: 256
- Processes: 64

**"Native" Mode** (broken): `--mode=native`
- Currently just runs interpreter
- Should use JIT compilation
- Needs implementation fix

## Verification Commands

```bash
# Check if JIT mode works directly
bin/simple --mode=jit test/runtime/runtime_parser_bugs_spec.spl

# Check if AOT compilation works
bin/simple compile test/runtime/runtime_parser_bugs_spec.spl -o /tmp/test_binary
/tmp/test_binary

# Check build system
bin/simple build --help

# List available compilation modes
grep "enum CompileMode" src/compiler/driver_types.spl -A10
```

## Summary

### What Was Wrong

❌ **Previous Report Said:** "Native mode doesn't exist, falls back to interpreter"

✅ **Reality:** Native compilation fully exists with:
- JIT compilation via Cranelift (working)
- AOT compilation to native binaries (working)
- Full compiler pipeline in `src/compiler/`
- Build system for native binaries in `src/compiler/build_native.spl`

### What IS Broken

❌ **Test runner's `--mode=native`:** Doesn't actually invoke native compilation
- Just passes test file to interpreter
- Should use `CompileMode.Jit` or compile to binary first

### What Works

✅ **Direct JIT compilation:** `simple --mode=jit file.spl`
✅ **AOT compilation:** `simple compile file.spl -o binary`
✅ **Build system:** `simple build --release`
✅ **Cranelift backend:** FFI to Cranelift for x86_64/aarch64/riscv64

## Next Steps

1. **Fix test runner native mode**
   - Implement true JIT compilation in `run_test_file_native()`
   - Use compiler API or shell out to `simple --mode=jit`

2. **Add test mode options**
   - `--mode=native` → JIT compile tests
   - `--mode=aot` → AOT compile tests to binaries

3. **Verify performance**
   - Compare interpreter vs JIT vs AOT performance
   - Benchmark test execution speed

4. **Documentation**
   - Update test runner docs
   - Add native mode examples

---

## References

- **Compiler Driver:** `src/compiler/driver.spl`
- **Codegen:** `src/compiler/codegen.spl`
- **JIT Context:** `src/compiler/loader/jit_context.spl`
- **Build Native:** `src/compiler/build_native.spl`
- **Test Runner:** `src/app/test_runner_new/test_runner_execute.spl`
- **Compile Modes:** `src/compiler/driver_types.spl` lines 64-88
