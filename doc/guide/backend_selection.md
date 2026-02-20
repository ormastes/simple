# Backend Selection Guide

The Simple compiler supports multiple backends (Cranelift, LLVM, C++20, Native, VHDL) with flexible selection via configuration.

## Quick Start

### Command Line Usage

```bash
# Auto-select backend (default: Cranelift for debug, LLVM for release)
bin/simple compile program.spl

# Force Cranelift backend
bin/simple compile --backend=cranelift program.spl

# Force LLVM backend
bin/simple compile --backend=llvm program.spl

# Generate C++20 source via MIR backend (single file)
bin/simple compile --backend=c -o program.cpp program.spl

# Then build with a C++ compiler:
clang++ -std=c++20 -O2 program.cpp src/compiler_seed/runtime.c -I src/compiler_seed -o program

# Or generate to directory and build with CMake + Ninja:
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build

# Cranelift with release optimizations
bin/simple compile --backend=cranelift --release program.spl

# LLVM for debug (faster optimization than release)
bin/simple compile --backend=llvm program.spl
```

## Backend Selection Rules

The compiler selects backends based on this priority:

### 1. Explicit Override (Highest Priority)

Set via `CompileOptions.backend`:

```simple
val options = CompileOptions(
    ...
    backend: "cranelift",  # Force Cranelift
    ...
)
```

Supported values:
- `"cranelift"` or `"clif"` → Cranelift JIT
- `"llvm"` → LLVM backend
- `"native"` → Direct machine code generation
- `"c"`, `"cpp"`, or `"ccodegen"` → C++20 source generation (MIR-based)
- `"vhdl"` → VHDL hardware description output
- `"interpreter"` or `"i"` → Tree-walk interpreter
- `"auto"` → Auto-select (see below)

### 2. Auto-Selection (Default)

When `backend = "auto"` (default), selection is based on build mode:

| Build Mode | Selected Backend | Reason |
|------------|------------------|---------|
| **Debug** | Cranelift | Fast compilation, quick iteration |
| **Release** | LLVM | Better optimization, smaller binaries |
| **Test** | Interpreter | No compilation overhead |
| **Bootstrap** | Cranelift | Minimal dependencies |

## Backend Comparison

### Cranelift

**Pros:**
- ✅ **Fast compilation** - 5-10x faster than LLVM
- ✅ Lightweight - minimal dependencies
- ✅ Good for development iteration
- ✅ Predictable compile times

**Cons:**
- ❌ Slower runtime (10-20% vs LLVM -O2)
- ❌ Basic optimizations only
- ❌ No advanced inlining/vectorization

**Best for:**
- Development builds
- Unit tests
- Quick prototyping
- CI builds (faster)

### LLVM

**Pros:**
- ✅ **Best optimization** - industry-leading
- ✅ Advanced vectorization (SIMD)
- ✅ Cross-function inlining
- ✅ Mature ecosystem

**Cons:**
- ❌ Slow compilation (10-50x slower than Cranelift)
- ❌ Large dependency
- ❌ Unpredictable compile times

**Best for:**
- Production releases
- Performance-critical code
- Benchmarking
- Shipping to users

### C++20 (MIR-based)

**Pros:**
- ✅ **Portable output** - C++20 compiles anywhere with clang++/g++
- ✅ **Bootstrap** - no LLVM/Cranelift needed, just a C++ compiler
- ✅ Readable output for debugging compiler internals
- ✅ Cross-compilation via C++ toolchain

**Cons:**
- ❌ Two-step process (generate C++ then compile it)
- ❌ No JIT support
- ❌ Optimization depends on the C++ compiler

**Best for:**
- Bootstrapping the compiler from scratch
- Cross-compilation to new targets
- Inspecting generated code
- Environments without LLVM/Cranelift

**Pipeline:** `source.spl → parse → HIR → MIR → MirToC → output.cpp`

**Usage:**
```bash
# Single-file output:
bin/simple compile --backend=c -o output.cpp source.spl
clang++ -std=c++20 -O2 output.cpp src/compiler_seed/runtime.c -I src/compiler_seed -o output

# Multi-file output (bootstrap):
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build
mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple
```

**Key files:**
- `src/compiler/backend/c_backend.spl` — MirToC translator + CCodegenBackend
- `src/compiler/backend/c_type_mapper.spl` — MIR type → C++ type mapping
- `src/compiler/backend/c_ir_builder.spl` — C++ source builder
- `src/compiler_cpp/CMakeLists.txt` — CMake build config for generated C++
- `src/app/compile/c_mir_backend.spl` — CLI entry script

## Programmatic Usage

### From Simple Code

```simple
use compiler.driver_types.{CompileOptions, CompileMode}
use compiler.backend.backend_factory.BackendFactory

# Create options with explicit backend
val options = CompileOptions(
    mode: CompileMode.Jit,
    backend: "llvm",  # Force LLVM
    release: true,
    ...
)

# Backend is created automatically by CompilerDriver
val driver = CompilerDriver.create(options)
val result = driver.compile()
```

### From CLI Parser

The CLI already supports `--backend` flag:

```bash
# Parse from command line
val backend_arg = args_get_flag("--backend", "auto")
val options = CompileOptions(
    ...
    backend: backend_arg,  # "cranelift", "llvm", or "auto"
    ...
)
```

## Advanced: Per-Function Backend Selection

Future enhancement - select backend per function:

```simple
@backend("llvm")  # Force LLVM for this hot function
fn matrix_multiply(a: Matrix, b: Matrix) -> Matrix:
    # Heavily optimized by LLVM
    ...

@backend("cranelift")  # Fast compilation for tests
fn test_helper():
    ...
```

## Environment Variables

Override backend via environment:

```bash
# Force Cranelift for all compilations
export SIMPLE_BACKEND=cranelift
bin/simple compile program.spl

# Force LLVM
export SIMPLE_BACKEND=llvm
bin/simple compile program.spl
```

## Configuration File

In `simple.toml`:

```toml
[build]
backend = "auto"  # or "cranelift", "llvm"

[build.debug]
backend = "cranelift"  # Fast iteration

[build.release]
backend = "llvm"  # Best performance
```

## Troubleshooting

### "Backend llvm does not support target"

LLVM may not support all targets. Use Cranelift as fallback:

```bash
bin/simple compile --backend=cranelift --target=riscv32 program.spl
```

### Slow compilation with LLVM

Use Cranelift for debug builds:

```bash
bin/simple compile --backend=cranelift program.spl
```

### Runtime performance issues

Use LLVM with release optimizations:

```bash
bin/simple compile --backend=llvm --release program.spl
```

## Implementation Details

**Backend Factory:** `src/compiler/backend/backend_factory.spl`
**Backend Helpers:** `src/compiler/backend/backend_helpers.spl`
**Driver:** `src/compiler/driver.spl`

The driver's `aot_compile()` method checks the backend name before format dispatch:
- If backend is `"c"`, `"cpp"`, or `"ccodegen"` → routes to `compile_to_c()` (writes C++ source)
- Otherwise → routes to `compile_to_native()` (links object files to executable)

```simple
# In CompilerDriver.aot_compile():
val backend_name = self.ctx.options.backend
if backend_name == "c" or backend_name == "cpp" or backend_name == "ccodegen":
    return self.compile_to_c(output)
# ... otherwise dispatch based on output format (native, smf, etc.)
```

`compile_module_with_backend()` in `backend_helpers.spl` handles the actual MIR translation:

```simple
case BackendKind.CCodegen:
    var c_translator = MirToC__create(module.name)
    val c_source = c_translator.translate_module(module)
    Ok(CompiledModule(name: module.name, object_code: nil, assembly: c_source, ...))
```

## Future Enhancements

1. **Profile-guided selection** - collect runtime data, optimize hot functions with LLVM
2. **Hybrid compilation** - Cranelift for debug info, LLVM for hot paths
3. **Per-module backends** - different backends for different modules
4. **Backend capability queries** - check what each backend supports
5. **Runtime switching** - switch backends during JIT compilation

## See Also

- `doc/guide/jit_compilation.md` - JIT compilation guide
- `doc/guide/optimization_levels.md` - Optimization flags
- `doc/design/core_full_unified_architecture.md` - Unified compiler architecture
- `src/compiler/backend/backend_factory.spl` - Backend factory implementation
- `src/compiler/backend/backend_types.spl` - Backend type definitions
- `src/compiler/backend/backend_helpers.spl` - Backend selection and compilation helpers
- `src/compiler/backend/c_backend.spl` - MIR-to-C++20 translator
- `src/compiler/driver.spl` - Compiler driver (compile_to_c, aot_compile)
