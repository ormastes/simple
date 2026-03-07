# Compiler Backends

**Version:** 0.5.0
**Status:** Production (Cranelift, C++20), Development (LLVM, Native, VHDL)

---

## Overview

Simple supports multiple compiler backends. Each backend translates MIR (Mid-level IR) to target code. The compiler automatically selects the best available backend, or you can choose manually.

---

## Available Backends

| Backend | Status | Use Case | Output |
|---------|--------|----------|--------|
| **Cranelift** | Production | Fast compilation, development | Native binary |
| **C++20** | Production | Portable, bootstrap | C++ source |
| **LLVM** | Development | Optimized release builds | Native binary |
| **Native** | Development | Direct machine code | Native binary |
| **VHDL** | Experimental | Hardware synthesis | VHDL source |

### Cranelift

Default backend for development. Fast compile times, good runtime performance.

```bash
bin/simple build                         # Uses Cranelift by default
bin/simple build --backend=cranelift     # Explicit
```

**Strengths:** Fast compilation (sub-second for small projects), good debugging support, cross-platform.
**Limitations:** Fewer optimizations than LLVM, no GPU code generation.

### C++20

Generates portable C++20 source code. Used for bootstrapping and maximum portability.

```bash
bin/simple build --backend=cpp
```

**Strengths:** Works anywhere with a C++20 compiler, easy to inspect generated code, good for debugging codegen.
**Limitations:** Two-stage compilation (Simple to C++ to binary), slower overall build.

### LLVM

Full LLVM optimization pipeline for release builds.

```bash
bin/simple build --backend=llvm --release
```

**Strengths:** Best runtime performance, mature optimization passes, GPU target support.
**Limitations:** Slower compilation, requires LLVM installation.

### Native

Direct machine code emission without intermediate representation.

```bash
bin/simple build --backend=native
```

**Strengths:** Fastest possible compilation, no external dependencies.
**Limitations:** Limited optimization, fewer target architectures.

### VHDL

Hardware description language output for FPGA synthesis.

```bash
bin/simple build --backend=vhdl --target=fpga
```

**Strengths:** Direct hardware synthesis from Simple source.
**Limitations:** Experimental, limited language feature support.

---

## Backend Selection

### Automatic Selection

The compiler picks the best backend based on context:

| Context | Selected Backend | Reason |
|---------|-----------------|--------|
| `build` (debug) | Cranelift | Fast compilation |
| `build --release` | LLVM (if available), else Cranelift | Best optimization |
| `build --target=wasm` | LLVM or Cranelift | WASM support |
| `build --target=fpga` | VHDL | Hardware target |
| No backends installed | C++20 | Always available |

### Manual Selection

```bash
bin/simple build --backend=cranelift   # Force Cranelift
bin/simple build --backend=llvm        # Force LLVM
bin/simple build --backend=cpp         # Force C++20
bin/simple build --backend=native      # Force Native
```

### Capability Detection

Check what backends are available:

```bash
bin/simple build --list-backends
```

Output:
```
Available backends:
  cranelift  [installed]  Fast compilation
  llvm       [installed]  Optimized builds (LLVM 17)
  cpp        [built-in]   C++20 output
  native     [installed]  Direct codegen
  vhdl       [missing]    Requires yosys
```

---

## Backend Capabilities

### Instruction Coverage

| Feature | Cranelift | LLVM | Native | C++20 |
|---------|-----------|------|--------|-------|
| Integer arithmetic | Full | Full | Full | Full |
| Floating point | Full | Full | Full | Full |
| SIMD/vectors | Partial | Full | Partial | Via intrinsics |
| Atomics | Full | Full | Full | Full |
| Exceptions | Partial | Full | No | Full |
| Debug info | DWARF | DWARF | Partial | Source maps |
| GPU kernels | No | CUDA/Vulkan | No | No |
| Tail calls | Yes | Yes | Yes | Compiler-dependent |

### Optimization Levels

| Level | Flag | Cranelift | LLVM | C++20 |
|-------|------|-----------|------|-------|
| None | `-O0` | No opts | No opts | `-O0` |
| Basic | `-O1` | Basic opts | Basic opts | `-O1` |
| Standard | `-O2` | Full opts | Full opts | `-O2` |
| Aggressive | `-O3` | Full opts | Aggressive | `-O3` |
| Size | `-Os` | Size opts | Size opts | `-Os` |

---

## Shared Backend Components

All backends share common infrastructure to ensure consistent behavior:

### TypeMapper

Translates Simple types to backend-specific representations:

```
Simple Type    Cranelift     LLVM          C++20
-----------    ---------     ----          -----
i32            types::I32    i32           int32_t
i64            types::I64    i64           int64_t
f32            types::F32    float         float
f64            types::F64    double        double
bool           types::I8     i1            bool
text           ptr           ptr           std::string
```

### LiteralConverter

Handles constant values consistently across backends:

- Integer literals with overflow checking
- Float literals with precision preservation
- String literals with escape sequence handling
- Boolean and unit literals

### ExpressionEvaluator

Translates MIR expressions to backend operations:

- Binary operations (arithmetic, comparison, logical)
- Unary operations (negation, bitwise not)
- Function calls and method dispatch
- Field access and array indexing

### Integration Pattern

Each backend implements a common interface:

```simple
trait Backend:
    fn compile(mir: MirModule) -> Result<Output, CompileError>
    fn supports_feature(feature: Feature) -> bool
    fn optimization_level() -> OptLevel
    fn target_triple() -> text
```

---

## MIR Optimization Passes

Before reaching the backend, MIR goes through optimization passes:

| Pass | Description | Impact |
|------|-------------|--------|
| Dead code elimination | Remove unreachable code | Code size |
| Constant folding | Evaluate compile-time constants | Speed |
| Inlining | Inline small functions | Speed |
| Common subexpression | Eliminate duplicate computations | Speed |
| Loop optimization | Strength reduction, unrolling | Speed |
| Collection optimization | Optimize collection patterns | Speed + allocations |
| Escape analysis | Stack-allocate non-escaping objects | Allocations |
| Tail call optimization | Convert tail calls to jumps | Stack usage |
| Branch simplification | Simplify conditional chains | Code size |
| Register allocation | Efficient register use | Speed |
| Memory-to-register | Promote stack vars to registers | Speed |
| Alias analysis | Track pointer aliasing | Enables other opts |

### Collection Optimization Patterns

The compiler automatically fixes common collection inefficiencies:

| Pattern | Anti-Pattern | Optimization |
|---------|-------------|--------------|
| COLL001 | `list.add()` in loop without `reserve()` | Auto-insert `reserve(n)` |
| COLL002 | String concat in loop | Use `StringBuilder` |
| COLL003 | `list.contains()` in loop | Convert to `Set` lookup |
| COLL004 | Redundant `sort()` calls | Eliminate duplicate sorts |
| COLL005 | Copy where move suffices | Use move semantics |
| COLL006 | `map.get()` + `map.put()` | Use `map.get_or_insert()` |
| COLL007 | Full copy for read-only use | Use reference/borrow |
| COLL008 | Unbounded collection growth | Suggest bounded alternatives |

---

## Cross-Compilation

### Target Specification

```bash
# Cross-compile for different architectures
bin/simple build --target=aarch64-linux
bin/simple build --target=x86_64-windows
bin/simple build --target=riscv32-baremetal
bin/simple build --target=wasm32-wasi
```

### Backend-Target Matrix

| Target | Cranelift | LLVM | Native | C++20 |
|--------|-----------|------|--------|-------|
| x86_64-linux | Yes | Yes | Yes | Yes |
| aarch64-linux | Yes | Yes | No | Yes |
| x86_64-macos | Yes | Yes | Yes | Yes |
| aarch64-macos | Yes | Yes | No | Yes |
| x86_64-windows | Yes | Yes | No | Yes |
| riscv32 | No | Yes | No | Yes |
| riscv64 | No | Yes | No | Yes |
| wasm32 | Yes | Yes | No | No |
| arm-baremetal | No | Yes | No | Yes |

---

## Performance Benchmarks

Relative performance (Cranelift = 1.0x baseline):

| Benchmark | Cranelift | LLVM -O2 | C++20 -O2 | Native |
|-----------|-----------|----------|-----------|--------|
| Compile time | 1.0x | 3.5x | 2.0x | 0.8x |
| Fibonacci(40) | 1.0x | 0.7x | 0.75x | 1.1x |
| String processing | 1.0x | 0.8x | 0.85x | 1.05x |
| Collection ops | 1.0x | 0.65x | 0.7x | 1.15x |
| Binary size | 1.0x | 0.6x | 0.8x | 1.3x |

Lower is better for all metrics. LLVM produces the fastest and smallest binaries but compiles slowest.

---

## Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| Backend not found | Not installed | `bin/simple build --list-backends` to check |
| LLVM version mismatch | Wrong LLVM version | Install LLVM 15-17 |
| Cranelift codegen error | Unsupported instruction | Try `--backend=llvm` |
| C++ compilation failure | Missing headers | Install C++20-capable compiler |
| Slow debug builds | Using LLVM for debug | Use `--backend=cranelift` for debug |
| Large binary size | No optimization | Add `--release` or `-Os` flag |

---

## Related Documentation

- GPU backends: `doc/guide/apps/gpu.md`
- Bare-metal targets: `doc/guide/backend/baremetal.md`
- Vulkan backend: `doc/guide/backend/vulkan.md`
