# Bootstrap Guide (2026-02-18)

This guide is the quick bootstrap reference for the current repository layout.

## Current Layout

- Full compiler sources: `src/compiler/`
- Generated C++20 output: `src/compiler_cpp/`
- Bootstrap scripts: `scripts/bootstrap/`

`src/compiler_core_legacy/` is retired. Bootstrap and docs should use `src/compiler/`.
Runtime files are in `src/runtime/` (previously `src/compiler_seed/`).

## C Backend Bootstrap (current pipeline)

The C backend emits C++20 from the full compiler and builds it with CMake + Ninja + Clang:

```bash
# 1. Generate C++20 from compiler source
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl

# 2. Build with CMake + Ninja
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build

# 3. Install bootstrap binary
mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple

# 4. Self-host verification
bin/bootstrap/cpp/simple build
```

Or use the bootstrap script:

```bash
scripts/bootstrap/bootstrap-c.sh              # Generate + build
scripts/bootstrap/bootstrap-c.sh --verify     # Generate + build + self-host verify
```

## Quick Commands

```bash
# C backend bootstrap (CMake + Ninja)
scripts/bootstrap/bootstrap-c.sh
scripts/bootstrap/bootstrap-c.sh --verify
```

## Script Map

- `scripts/bootstrap/bootstrap-c.sh`: C backend bootstrap (CMake + Ninja)

## Expected Output

- Final binary: `bin/release/simple` — **fully self-sufficient** (all compilation, interpretation, and test running happens in-process via direct function calls like `aot_c_file()`, `compile_native()`, `interpret_file()`)
- C backend bootstrap binary: `bin/bootstrap/cpp/simple`
- Intermediate artifacts: `build/bootstrap/`

## Architecture Note (2026-02-28)

The self-hosted binary (`bin/release/simple`) no longer delegates any work to subprocess calls. All compilation backends (C, VHDL, native), file execution, and test running use in-process function calls. The only external tool calls are system compilers/linkers: `clang`/`clang++`, `gcc`, `mold`/`lld`/`ld`, `llc`, `uname`, `which`.

## Related Docs

- `doc/build/bootstrap_pipeline.md`
