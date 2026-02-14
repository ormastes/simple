# Backend Selection Guide

The Simple compiler supports multiple backends (Cranelift and LLVM) with flexible selection via configuration.

## Quick Start

### Command Line Usage

```bash
# Auto-select backend (default: Cranelift for debug, LLVM for release)
bin/simple compile program.spl

# Force Cranelift backend
bin/simple compile --backend=cranelift program.spl

# Force LLVM backend
bin/simple compile --backend=llvm program.spl

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
- `"native"` or `"c"` → Native C backend
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

**File:** `src/compiler_core/backend/backend_factory.spl`

```simple
# Backend selection logic
fn create(target: CodegenTarget, options: CompileOptions) -> Backend:
    # 1. Check explicit override
    val backend_kind = backendkind_from_text(options.backend)
    if backend_kind != nil:
        return create_specific(backend_kind, target, options)

    # 2. Auto-select based on build mode
    val mode = if options.release: BuildMode.Release else: BuildMode.Debug
    val auto_kind = auto_select(target, mode)
    return create_specific(auto_kind, target, options)
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
- `src/compiler_core/backend/backend_factory.spl` - Implementation
- `src/compiler_core/backend_types.spl` - Backend types
