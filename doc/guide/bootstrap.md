# Bootstrap Guide

How to build the Simple compiler from source using the seed compiler chain.

## Overview

Simple is a self-hosting compiler — it's written in Simple. To build it from source, we need a "seed" compiler that can compile Simple code without requiring an existing Simple compiler.

The bootstrap chain:

```
seed.cpp (C++) ──clang++──> seed_cpp (binary)
seed_cpp + compiler_core/*.spl ──transpile──> core1.cpp (C++)
core1.cpp ──clang++──> Core1 (native binary, minimal compiler)
Core1 + compiler_core/*.spl ──compile──> Core2 (reproducibility check)
Core2 + full compiler source ──compile──> Full1 (full compiler)
Full1 + full compiler source ──compile──> Full2 (reproducibility check)
```

If Full1 == Full2 (same hash), the bootstrap is verified as reproducible.

## Prerequisites

| Requirement | Purpose | Install |
|-------------|---------|---------|
| `bin/release/simple` | Pre-built runtime (33MB) | Included in repo |
| `seed/build/seed_cpp` | Seed C++ transpiler (81KB) | Build from `seed/` |
| `clang++` | C++20 compiler | `sudo apt install clang` |
| `seed/build/libspl_runtime.a` | Runtime library | Built with seed |
| `seed/build/startup/libspl_crt_linux_x86_64.a` | Startup CRT | Built with seed |

### Building seed artifacts

```bash
cd seed/build
cmake ..
cmake --build . --parallel $(nproc)
```

This produces `seed_cpp`, `libspl_runtime.a`, and `libspl_crt_linux_x86_64.a`.

## Quick Start

```bash
bin/release/simple script/bootstrap-multiphase.spl --keep-artifacts
```

Options:
- `--no-verify` — Skip reproducibility checks (faster)
- `--keep-artifacts` — Keep intermediate binaries in `build/bootstrap/`
- `--seed-cpp=PATH` — Custom seed_cpp path
- `--clang=PATH` — Custom clang++ path

## Manual Steps

If you want to run each phase manually:

### Phase 1: Core1 (seed_cpp to native)

```bash
# 1. Discover and order compiler_core files
FILES=$(find src/compiler_core/ -name '*.spl' | sort)

# 2. Transpile to C++
seed/build/seed_cpp $FILES > build/bootstrap/core1.cpp

# 3. Compile with clang++
clang++ -std=c++20 -O2 \
  -o build/bootstrap/core1 \
  build/bootstrap/core1.cpp \
  -Iseed \
  -Lseed/build -lspl_runtime \
  -lm -lpthread

# 4. Verify
ls -la build/bootstrap/core1
./build/bootstrap/core1 --version
```

### Phase 2: Core2 (reproducibility)

```bash
./build/bootstrap/core1 compile src/compiler_core/main.spl \
  -o build/bootstrap/core2

# Compare hashes
sha256sum build/bootstrap/core1 build/bootstrap/core2
```

### Phase 3: Full1 (full compiler)

```bash
./build/bootstrap/core2 compile src/app/cli/main.spl \
  -o build/bootstrap/full1
```

### Phase 4: Full2 (reproducibility)

```bash
./build/bootstrap/full1 compile src/app/cli/main.spl \
  -o build/bootstrap/full2

# Compare hashes — should match
sha256sum build/bootstrap/full1 build/bootstrap/full2
```

### Install

```bash
cp build/bootstrap/full2 bin/simple
chmod +x bin/simple
```

## Architecture

```
                    seed.cpp
                       |
                   [clang++]
                       |
                       v
                    seed_cpp  ←── Minimal C++ transpiler
                       |          Reads Core Simple, emits C++
                       |          Two-pass: signatures then bodies
                       |
        compiler_core/*.spl ──[seed_cpp]──> core1.cpp
                                               |
                                           [clang++]
                                               |
                                               v
                                            Core1  ←── Minimal native compiler
                                               |
                    compiler_core/*.spl ──[Core1]──> Core2
                                                        |
                          src/app/cli/main.spl ──[Core2]──> Full1
                                                               |
                          src/app/cli/main.spl ──[Full1]──> Full2
                                                               |
                                                       [verify Full1==Full2]
                                                               |
                                                           bin/simple
```

### Seed compiler (seed_cpp)

The seed compiler (`seed/seed.cpp`) is ~3400 lines of C++ that:
- Parses Core Simple (a strict subset: no generics, traits, lambdas)
- Emits C++ code with forward declarations (two-pass)
- Links against `libspl_runtime.a` for runtime support

Current limits (configurable in `seed/seed.cpp`):
- MAX_LINES: 100,000 (compiler_core is ~44K)
- MAX_FUNCS: 4,096 (compiler_core has ~1,750)
- MAX_METHODS: 4,096 (compiler_core has ~260)
- MAX_STRUCTS: 1,024 (compiler_core has ~500)
- MAX_ENUMS: 512 (compiler_core has ~220)

### Compiler core (compiler_core/)

A desugared version of the compiler written in Core Simple — the subset that seed_cpp can handle. No generics, no traits, no lambdas, no class (uses struct+impl instead).

## Troubleshooting

### seed_cpp compilation fails

**"MAX_LINES exceeded"** — Increase `MAX_LINES` in `seed/seed.cpp` and rebuild:
```bash
# Edit seed/seed.cpp: change MAX_LINES from 100000 to 200000
cd seed/build && cmake --build . --parallel
```

**"MAX_FUNCS exceeded"** (or MAX_METHODS, MAX_STRUCTS, MAX_ENUMS) — Same approach: increase the constant in `seed/seed.cpp` and rebuild.

### clang++ compilation of C++ fails

- Check you have C++20 support: `clang++ -std=c++20 -x c++ /dev/null -c -o /dev/null`
- Check `runtime.h` is findable: the `-Iseed` flag should point to the directory containing it
- Check `libspl_runtime.a` is built: `ls -la seed/build/libspl_runtime.a`

### Core1 binary is too small

If the binary is under 10KB, seed_cpp likely produced empty/stub output. Check:
- `wc -l build/bootstrap/core1.cpp` — should be thousands of lines
- Look for errors in seed_cpp stderr

### Core1 can't compile (Phase 2 fails)

The compiler_core may use features not yet supported by the seed-built compiler. Check error messages. The seed path only needs to bootstrap enough to get a self-hosting cycle going.

### Reproducibility check fails

Core1 vs Core2 hash mismatch is expected — they are built by different compilers (clang++ vs the self-hosted compiler). Full1 vs Full2 should match since both are built by the same compiler.

## Verification

A successful bootstrap verifies:
1. The seed compiler can transpile compiler_core to valid C++
2. The transpiled compiler can compile itself (self-hosting)
3. The full compiler can compile itself reproducibly (Full1 == Full2)

To verify independently:
```bash
# Check all test pass with the new compiler
bin/simple test

# Compare with reference binary
sha256sum bin/simple bin/release/simple
```
