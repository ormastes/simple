# Building Core Simple: Seed, CMake, and Clang Guide

This guide covers the seed compiler, the CMake build system, and how to build
the Core Simple library from `.spl` source to native C using clang.

---

## Overview

The Simple compiler is self-hosted: the compiler is written in Simple itself.
To bootstrap from scratch, a **seed compiler** (written in pure C/C++) compiles
the initial Simple source into C code. The generated C is then compiled by
clang into a native binary.

```
Simple source (.spl)
        │
        ▼
┌─────────────────┐     ┌──────────────────┐
│ Seed Compiler    │ OR  │ Simple Compiler   │
│ (seed.c/seed.cpp)│     │ (bin/simple)      │
└────────┬────────┘     └────────┬─────────┘
         │                       │
         ▼                       ▼
    Generated C code (.c)
         │
         ▼
┌─────────────────┐
│ clang (C11)     │
└────────┬────────┘
         │
         ▼
   Native binary
```

---

## Directory Structure

```
seed/
├── seed.c              # Bootstrap seed compiler (C, ~2000 lines)
├── seed.cpp            # C++ seed compiler for Core Simple
├── runtime.h           # Runtime header: tagged values, arrays, dicts
├── runtime.c           # Runtime implementation: string ops, arrays, I/O
├── CMakeLists.txt      # CMake build configuration
├── seed_test.cpp       # Seed compiler integration tests
├── runtime_test.c      # Runtime library tests
├── c_runtime_test.c    # Static C runtime helper tests
└── startup/            # Platform CRT (C Runtime) startup
    ├── CMakeLists.txt
    ├── common/
    │   ├── crt_common.h
    │   └── crt_common.c
    ├── linux/
    │   ├── crt_linux.c
    │   └── x86_64/start.S, x86/start.S, arm64/start.S, riscv64/start.S
    ├── macos/
    │   ├── crt_macos.c
    │   └── x86_64/start.S, arm64/start.S
    ├── windows/
    │   ├── crt_windows.c
    │   └── x86_64/start.S, x86/start.S, arm64/start.S
    ├── freebsd/
    │   └── ...
    └── baremetal/
        └── ...

src/app/compile/       # C codegen (all in Simple)
├── c_codegen.spl      # Main generator: type registry, pre-pass, struct/enum/fn handling
├── c_translate.spl    # Expression/statement/control flow translation
├── c_helpers.spl      # Type queries, indent, signature parsing
├── c_runtime.spl      # Runtime code embedding
├── c_runtime.c        # Static C helpers embedded in generated code
├── native.spl         # Native compilation pipeline (Simple→C→binary)
└── gen_c_only.spl     # C-only generation utility
```

---

## Prerequisites

- **clang** (C11 support required, clang 14+ recommended)
- **cmake** 3.20+
- **Simple compiler** (`bin/simple` or `bin/release/simple`)

### Verify Tools

```bash
clang --version     # Should show clang 14+
cmake --version     # Should show 3.20+
```

---

## Building the Seed Compiler with CMake

The seed compiler and runtime are built using CMake. The CMake configuration
automatically prefers clang when available.

### Quick Build

```bash
cd seed

# Configure (clang is auto-detected)
cmake -B build -DCMAKE_BUILD_TYPE=Release

# Build all targets
cmake --build build

# Run tests
cmake --build build --target runtime_test
./build/runtime_test

cmake --build build --target seed_test
./build/seed_test
```

### Explicit Clang Selection

If clang is not auto-detected, specify it explicitly:

```bash
cmake -B build \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++ \
    -DCMAKE_BUILD_TYPE=Release

cmake --build build
```

### Build with Coverage

LLVM source-based coverage requires clang:

```bash
cmake -B build-coverage \
    -DCOVERAGE=ON \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++

cmake --build build-coverage
```

### CMake Targets

| Target | Description |
|--------|-------------|
| `seed` | C bootstrap seed compiler |
| `seed_cpp` | C++ seed compiler for Core Simple |
| `spl_runtime` | Static runtime library (`libspl_runtime.a`) |
| `runtime_test` | Runtime library test suite |
| `c_runtime_test` | Static C runtime helper tests |
| `seed_test` | Seed compiler integration tests |

---

## Generating C from Simple Source

The C code generator translates `.spl` files into standalone C code that
includes an embedded runtime. There are two methods:

### Method 1: Using native.spl (Recommended)

```bash
# Generate C only (no compilation)
bin/simple src/app/compile/native.spl src/compiler_core/tokens.spl /tmp/core_tokens --gen-c-only

# The generated file is at /tmp/core_tokens (no .c extension)
# Verify with clang:
clang -fsyntax-only -x c /tmp/core_tokens
```

### Method 2: Using gen_c_only.spl

```bash
bin/simple src/app/compile/gen_c_only.spl src/compiler_core/tokens.spl /tmp/core_tokens.c
```

### Method 3: Full Native Compilation

```bash
# Compile Simple source directly to native binary
bin/simple src/app/compile/native.spl src/compiler_core/tokens.spl /tmp/tokens_binary --verbose

# With explicit clang:
bin/simple src/app/compile/native.spl src/compiler_core/tokens.spl /tmp/tokens_binary --compiler clang
```

---

## Building Core Simple Modules

Core Simple (`src/compiler_core/`) contains 18 modules that form the compiler's core
library. Each can be compiled individually to C.

### Individual Module Compilation

```bash
# Generate C for a single module
bin/simple src/app/compile/native.spl src/compiler_core/tokens.spl /tmp/core_tokens --gen-c-only

# Verify with clang
clang -fsyntax-only -x c /tmp/core_tokens
```

### Batch Verification (All 18 Modules)

```bash
for f in tokens types error ast ast_types lexer_types hir_types mir_types \
         backend_types __init__ mir lexer lexer_struct parser test_core \
         aop aop_debug_log test_lang_basics; do
    bin/simple src/app/compile/native.spl src/compiler_core/${f}.spl /tmp/core_${f} --gen-c-only 2>/dev/null
    errs=$(clang -fsyntax-only -x c /tmp/core_${f} 2>&1 | grep -c 'error:' || true)
    echo "${f}: ${errs} errors"
done
```

### Module Status

Modules that compile to valid C with zero errors (standalone):

| Module | Status | Notes |
|--------|--------|-------|
| `tokens` | Clean | Token definitions, keyword lookup |
| `types` | Clean | Type system definitions |
| `ast` | Clean | AST node types |
| `ast_types` | Clean | AST type definitions |
| `lexer_types` | Clean | Lexer type definitions |
| `hir_types` | Clean | HIR type definitions |
| `mir_types` | Clean | MIR type definitions |
| `backend_types` | Clean | Backend type definitions |
| `__init__` | Clean | Module initialization |
| `mir` | Clean | MIR (Mid-level IR) |
| `test_lang_basics` | Clean | Language feature tests |
| `error` | Cross-file deps | Needs `int_to_str` from `types` |
| `lexer` | Cross-file deps | Needs `TOK_*` from `tokens` |
| `lexer_struct` | Cross-file deps | Needs `TOK_*` from `tokens` |
| `parser` | Cross-file deps | Needs tokens, lexer symbols |
| `test_core` | Cross-file deps | Needs `TOK_*`, test helpers |
| `aop` | Codegen WIP | Struct array + enum returns |
| `aop_debug_log` | 1 error | Tuple return `.len()` |

---

## Code Generation Architecture

The C codegen is a text-to-text translator (not AST-based). It processes
Simple source line-by-line, maintaining a type registry for correct C output.

### Pipeline

```
Simple source text
    │
    ▼
c_codegen.spl: generate_c_code()
    ├── Pre-pass: join multi-line expressions
    ├── Enum/struct/class scanning
    ├── Forward declaration generation
    ├── Function body translation
    │   └── c_translate.spl
    │       ├── translate_condition()   – and/or/not, string comparisons
    │       ├── translate_expr()        – arithmetic, calls, indexing
    │       ├── translate_statement()   – assignments, control flow
    │       ├── translate_for_loop()    – range, array, struct iteration
    │       └── translate_case()        – match/case patterns
    ├── close_blocks()                  – indentation-based brace closing
    ├── build_function()                – function assembly + var dedup
    └── c_runtime.c embedding           – static helper functions
    │
    ▼
Generated C code (single .c file)
    │
    ▼
clang -o binary generated.c
```

### Type Registry

The codegen threads a string-based type registry through all functions:

```
;text:var_name;arr:array_name;fn_text:func_name;struct:StructName;
;struct_arr_var:name=ElementType;field_struct_arr:Class.field=ElementType;
```

Type entries are appended as variables are discovered. Functions return
`"code|||;type_entry1;type_entry2;"` with `|||` separator when they add
new type information.

### Supported C Types

| Simple Type | C Type |
|-------------|--------|
| `i64` | `long long` |
| `bool` | `int` |
| `text` / `str` | `const char*` |
| `f64` | `double` |
| `[text]` | `SimpleStringArray` |
| `[i64]` | `SimpleIntArray` |
| `[[text]]` | `SimpleStringArrayArray` |
| `[[i64]]` | `SimpleIntArrayArray` |
| `[StructName]` | `SimpleStructArray` |
| `Option<T>` | `SimpleOption` |
| `Dict` | `SimpleDict*` |
| `StructName` | `StructName` (C struct) |

---

## Cross-File Compilation (Phase 2)

For modules with cross-file dependencies, the native pipeline supports
multi-file compilation by collecting dependencies via BFS:

```bash
# native.spl automatically discovers and merges dependencies
bin/simple src/app/compile/native.spl src/compiler_core/__init__.spl /tmp/core_combined --gen-c-only --verbose
```

The pipeline:
1. Scans `use` imports in the source file
2. Resolves module paths to `.spl` files
3. BFS-walks transitive dependencies
4. Concatenates all dependency sources before the main source
5. Generates a single unified `.c` file

---

## Compiling Generated C with Clang

### Syntax Check Only

```bash
# -x c tells clang the input is C (needed when file has no .c extension)
clang -fsyntax-only -x c /tmp/core_tokens
```

### Compile to Object File

```bash
clang -c -fPIE -o /tmp/core_tokens.o -x c /tmp/core_tokens
```

### Compile to Executable

```bash
clang -o /tmp/tokens_binary -x c /tmp/core_tokens
```

### With Optimizations

```bash
clang -O2 -o /tmp/tokens_opt -x c /tmp/core_tokens
```

### Common Flags

| Flag | Purpose |
|------|---------|
| `-fsyntax-only` | Check syntax without generating code |
| `-x c` | Treat input as C source (for extensionless files) |
| `-fPIE` | Position-independent executable |
| `-O2` | Optimization level 2 |
| `-Wall -Wextra` | Enable warnings |
| `-fuse-ld=mold` | Use mold linker (Linux, faster) |
| `-fprofile-instr-generate -fcoverage-mapping` | LLVM coverage |

---

## Platform CRT Startup

The seed startup code provides minimal C runtime initialization for
freestanding environments. Each platform has:

- **C entry point** (`crt_<platform>.c`): Sets up stack, calls `main()`
- **Assembly entry** (`start.S`): Architecture-specific `_start` symbol

Supported platforms and architectures:

| Platform | x86 | x86_64 | arm64 | riscv64 |
|----------|-----|--------|-------|---------|
| Linux | Yes | Yes | Yes | Yes |
| macOS | - | Yes | Yes | - |
| Windows | Yes | Yes | Yes | - |
| FreeBSD | Yes | Yes | - | - |
| Baremetal | Yes | Yes | Yes | Yes |

Build startup libraries:

```bash
cd seed
cmake -B build -DCMAKE_C_COMPILER=clang
cmake --build build
# Startup libraries are built as part of the main build
```

---

## Troubleshooting

### clang not found

```bash
# Install clang (Ubuntu/Debian)
sudo apt install clang

# Or specify path explicitly
cmake -B build -DCMAKE_C_COMPILER=/usr/bin/clang-20
```

### Generated file has no .c extension

The `--gen-c-only` flag generates files without a `.c` extension. Use `-x c`
with clang:

```bash
clang -fsyntax-only -x c /tmp/core_tokens
```

### Cross-file dependency errors

Errors like `use of undeclared identifier 'TOK_KW_FN'` indicate cross-file
dependencies. These modules need multi-file compilation (Phase 2) where
dependencies are merged before code generation.

### Coverage build fails

Coverage requires clang (not gcc):

```bash
cmake -B build -DCOVERAGE=ON \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++
```
