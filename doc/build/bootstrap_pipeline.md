# Bootstrap Pipeline — Seed / Core / Full

## Architecture

The Simple compiler bootstraps through 3 layers, from C++ to self-hosting Simple:

```
seed (C++)  -->  core (Simple)  -->  full (Simple)
```

| Layer | Language | Source | Output | Purpose |
|-------|----------|--------|--------|---------|
| **seed** | C++ | `seed/seed.cpp` (3,437 lines) | C++ transpiler binary | Transpile Core Simple to C++ |
| **core** | Core Simple | `src/core/` (20,053 lines, 31 files) | Native compiler binary | Compile Full Simple |
| **full** | Full Simple | `src/compiler/` (127,284 lines, 409 files) | Self-hosting compiler | The production compiler |

### Bootstrap Chain

```
Step 1 (bootstrap):  clang++ seed.cpp --> seed binary (Mach-O/ELF)
Step 2 (seed):       seed reads src/core/*.spl --> core_compiler.cpp (C++)
Step 3 (core1):      clang++ core_compiler.cpp + runtime.c --> core_compiler binary
Step 4 (core2):      core_compiler compiles src/core/*.spl --> core_self.cpp (self-check)
Step 5 (full1):      core_compiler compiles src/compiler/*.spl --> full compiler
Step 6 (full2):      full compiler compiles src/compiler/*.spl --> full compiler v2 (self-check)
Step 7 (simple):     SHA256(full1) == SHA256(full2) --> verified self-hosting binary
Step 8 (build):      Copy verified binary --> bin/release/<platform>/simple
```

## Seed Layer (C++)

**Files:** `seed/`

| File | Lines | Purpose |
|------|-------|---------|
| `seed.cpp` | 3,437 | Simple-to-C++ transpiler |
| `seed.c` | 2,067 | Alternative C transpiler |
| `runtime.c` | 970 | C runtime (arrays, strings, dicts, GC) |
| `runtime.h` | 244 | Runtime API headers |
| `CMakeLists.txt` | 75 | CMake build config |

**Supported Core Simple subset:**
- `val`/`var` declarations, `fn` with typed params, `extern fn`
- `struct`, `enum` (simple variants), `impl` blocks
- `if`/`elif`/`else`, `for` (range + array), `while`, `match`/`case`
- `return`, `break`, `continue`
- Array literals, string interpolation, `use`/`export`

**NOT supported (Full Simple only):**
- Generics `<T>`, traits, `class`, `actor`, `async`/`await`
- Lambdas, comprehensions, pipe operators `|>`
- Math blocks, GPU kernels, bitfields, pattern binding

**Build command:**
```bash
cd build/cmake && cmake ../../seed && make
# or: clang++ -std=c++20 -o build/bootstrap/seed seed/seed.cpp
```

## Core Layer (Pure Simple)

**Directory:** `src/core/` — 31 .spl files, 20,053 lines

**Key modules:**
- `ast.spl`, `ast_types.spl` — Abstract Syntax Tree
- `parser.spl` — Parser
- `lexer.spl`, `lexer_struct.spl`, `lexer_types.spl` — Lexer
- `tokens.spl` — Token definitions
- `types.spl` — Type system
- `mir.spl`, `mir_types.spl` — Mid-level IR
- `hir_types.spl` — High-level IR
- `error.spl` — Error handling
- `compiler/c_codegen.spl` — C code generation
- `compiler/driver.spl` — Compilation driver
- `interpreter/` — Runtime interpreter (env, eval, ops, value, jit)

**Build process:**
```bash
# seed transpiles Core Simple to C++
build/bootstrap/seed src/core/__init__.spl > build/bootstrap/core_compiler.cpp

# Compile C++ to native binary
clang++ -std=c++20 -o build/bootstrap/core_compiler \
    build/bootstrap/core_compiler.cpp seed/runtime.c -Iseed
```

**Generated output:** `core_compiler.cpp` (~9,747 lines C++, 370 KB)

## Full Layer (Pure Simple)

**Directory:** `src/compiler/` — 409 .spl files, 127,284 lines

**Key modules:**
- `lexer/` — Full lexical analysis
- `parser/` — Full parser
- `hir/` — High-level IR (extended)
- `mir/` — Mid-level IR (extended)
- `codegen/` — Code generation (C/LLVM/Cranelift)
- `backend/` — Multiple backends (47+ files)
- `resolve/` — Name resolution
- `type_infer/` — Type inference
- `dependency/` — Dependency resolution
- `semantics/` — Semantic analysis
- `lint/` — Linter
- `type_system/` — Full type system

**Entry point:** `src/compiler/main.spl`

**Build process:**
```bash
# Core compiler compiles Full Simple
build/bootstrap/core_compiler src/compiler/main.spl > build/bootstrap/full_compiler.cpp
clang++ -std=c++20 -o build/bootstrap/full1 \
    build/bootstrap/full_compiler.cpp seed/runtime.c -Iseed

# Self-hosting verification
build/bootstrap/full1 src/compiler/main.spl > build/bootstrap/full2_compiler.cpp
clang++ -std=c++20 -o build/bootstrap/full2 \
    build/bootstrap/full2_compiler.cpp seed/runtime.c -Iseed

# Verify reproducibility
sha256sum build/bootstrap/full1 build/bootstrap/full2  # Must match
```

## Current Status (2026-02-12)

### Linux

| Stage | Status | Artifact | Notes |
|-------|--------|----------|-------|
| seed | ? | N/A | Not verified (no Linux env) |
| core1 | ? | N/A | Not verified |
| core2 | ? | N/A | Not verified |
| full1 | ? | N/A | Not verified |
| full2 | ? | N/A | Not verified |
| simple | Exists | `bin/release/linux-x86_64/simple` (33 MB) | Pre-built Linux ELF x86-64 |

**Note:** A 33 MB pre-built binary exists, but the pipeline has not been verified end-to-end on Linux from seed.cpp.

### macOS (arm64)

| Stage | Status | Artifact | Size |
|-------|--------|----------|------|
| bootstrap | PASS | `build/cmake/seed`, `build/cmake/seed_cpp` | 67K, 84K |
| seed | PASS | `build/bootstrap/seed` (Mach-O arm64) | 67K |
| core1 | PASS | `build/bootstrap/core_compiler` (Mach-O arm64) | 326K |
| core2 (minimal) | **PASS** | `build/bootstrap/core_compiler_v2_minimal` (Mach-O arm64) | 207K |
| core3 (fixpoint) | **PASS** | `build/bootstrap/core_compiler_v3` (Mach-O arm64) | 207K |
| full1 | **BLOCKED** | OOM at ~216/373 files (~85GB peak on 24GB system) | — |
| full2 | BLOCKED | Not attempted (full1 OOM) | — |
| simple | **WRONG** | `bin/release/macos-arm64/simple` is Linux ELF, not Mach-O! | 33M |

**Core2 fixed point achieved (2026-02-12):**
- `parser.spl` fixed: added `parse_binary_from()` and named constructor arg support in `parse_call_arg()`
- Minimal file set (9 files): tokens, types, error, lexer, ast_types, ast, parser, c_codegen, driver
- v2 and v3 produce **byte-for-byte identical C++ output**
- SHA256: `0407d9fbf331ec2b441d17c0f659b9d938dfaf527151d37bc7d6e4a06257fa76`
- Note: `lexer_types.spl` and `lexer_struct.spl` excluded due to conflicting `span_new`/`token_new` definitions with `types.spl`

**Full1 memory issue:**
- core_compiler processes up to ~215 files before OOM-kill on 24GB system
- Memory scales super-linearly: 19MB (1 file) → 52GB (100 files) → 84GB+ (200 files)
- Two-batch workaround produces valid C++ per batch (~24K + ~17K lines) but batches are incompatible (each has own `main()`)
- Generated C++ also has: `struct char` keyword collision, forward declaration ordering issues

### Release Binary Issue

**ALL** release binaries in `bin/release/` are Linux x86-64 ELF:

| Directory | Expected | Actual | SHA1 |
|-----------|----------|--------|------|
| `linux-x86_64/` | Linux x86-64 | Linux x86-64 | `8108cbb...` |
| `simple` (root) | Linux x86-64 | Linux x86-64 | `8108cbb...` |
| `linux-arm64/` | Linux arm64 | **Linux x86-64** | `484854f...` |
| `linux-riscv64/` | Linux riscv64 | **Linux x86-64** | `484854f...` |
| `macos-arm64/` | Mach-O arm64 | **Linux x86-64** | `484854f...` |
| `macos-x86_64/` | Mach-O x86-64 | **Linux x86-64** | `484854f...` |

Only 2 unique binaries exist (different hashes). Non-linux-x86_64 are placeholders.

## Build Artifacts

```
build/bootstrap/
  seed                      67K   Mach-O arm64  -- C++ seed compiler
  seed_cpp                  84K   Mach-O arm64  -- Alternative seed
  core_compiler.cpp         370K  C++ source    -- Generated by seed from src/core/
  core_compiler             326K  Mach-O arm64  -- Compiled core (stage 1)
  core_self_minimal2.cpp    310K  C++ source    -- core_compiler self-compile (9 minimal files, 8016 lines)
  core_compiler_v2_minimal  207K  Mach-O arm64  -- Self-hosted core v2 (WORKING)
  core_compiler_v3          207K  Mach-O arm64  -- Self-hosted core v3 (FIXED POINT with v2)
  runtime.o                 24K   Object        -- Runtime library
```

## Required Fixes

### ~~P0: Core self-compilation (core2)~~ RESOLVED
Core self-hosting fixed point achieved with 9 minimal files. `parser.spl` fixed to support named constructor args and binary expression parsing after consumed identifiers. SHA256 match between v2 and v3 confirmed.

### P1: Full compilation (full1) — BLOCKED by memory
The `core_compiler` OOMs at ~216 files on 24GB system. Options:
1. **Optimize memory** in core_compiler (AST/symbol table likely has quadratic growth or leaks)
2. **Incremental compilation** — compile batches, merge C++ output manually
3. **Use a machine with more RAM** (needs ~85GB+ for 373 files)
4. **Reduce full compiler size** — the 373 files / 124K lines may be reducible

Additional C++ codegen issues in generated full1 output:
- `struct char` — reserved keyword collision (rename to `spl_char`)
- Forward declaration ordering — struct types used before defined
- Type references across batch boundaries

### P2: Full self-hosting (full2)
Blocked by P1. Once full1 produces a working compiler, it must compile itself reproducibly.

### P3: Native release binaries
Replace Linux ELF placeholders in `bin/release/` with actual native binaries for each platform.

## Related Files

| File | Purpose |
|------|---------|
| `seed/seed.cpp` | C++ seed transpiler |
| `seed/runtime.c` | C runtime library |
| `seed/CMakeLists.txt` | CMake build config for seed |
| `src/core/` | Core Simple source (compiled by seed) |
| `src/compiler/` | Full Simple source (compiled by core) |
| `src/compiler/main.spl` | Full compiler entry point |
| `src/core/compiler/c_codegen.spl` | C code generation in Core Simple |
| `src/core/compiler/driver.spl` | Compilation driver in Core Simple |
| `build/bootstrap/` | Build artifacts |
| `build/cmake/` | CMake build directory |
