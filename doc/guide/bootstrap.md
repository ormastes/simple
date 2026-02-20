# Bootstrap Guide (2026-02-18)

This guide is the quick bootstrap reference for the current repository layout.

## Current Layout

- Core sources: `src/compiler_core/`
- Full compiler sources: `src/compiler/`
- Generated C++20 output: `src/compiler_cpp/`
- Bootstrap scripts: `scripts/bootstrap/`

`src/compiler_core_legacy/` is retired. Bootstrap and docs should use `src/compiler/`.

## Bootstrap Pipeline

1. `seed` compiles Core Simple sources.
2. `core1` compiles core/full Simple sources.
3. `core2` verifies self-hosting for core.
4. `full1` compiles full compiler/app entry.
5. `full2` recompiles for reproducibility check.

See detailed pipeline: `doc/build/bootstrap_pipeline.md`.

## C Backend Bootstrap

The C backend generates C++20 from Simple source, which is then built with CMake + Ninja + Clang:

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

## Shared Frontend Contract

Frontend logic is shared, not duplicated:

- Core frontend runner: `src/compiler_core/frontend.spl`
- Full frontend runner: `src/compiler/frontend.spl`

Core compiler/interpreter and full compiler paths must call these shared entrypoints.

## Seed/Core Conditional Compile

Seed and core now support source-level conditional directives:

- `#if <condition>`
- `#elif <condition>`
- `#else`
- `#endif`

Trailing `:` is also accepted (`#if linux:`, `#else:`), matching Simple block style.

Common conditions:

- OS: `win`, `windows`, `linux`, `mac`, `macos`, `darwin`, `freebsd`, `openbsd`, `netbsd`, `android`, `unix`
- CPU/arch: `x86_64`, `x86`, `aarch64`, `arm`, `riscv64`, `riscv32`, `ppc64le`
- Key/value: `os=linux`, `arch=x86_64`, `cpu=arm64`

Override target detection during bootstrap with:

- `SIMPLE_TARGET_OS`
- `SIMPLE_TARGET_ARCH`
- `SIMPLE_TARGET_CPU`

Full compiler frontend also uses the same core conditional preprocessing path
(`src/compiler/frontend.spl` -> `core.parser.preprocess_conditionals`) so
`#if/#elif/#else/#endif` behavior is consistent across core and full runs.

OpenBSD/NetBSD currently share the POSIX runtime path and use the FreeBSD
startup CRT path in seed bootstrap (Tier 2 support).

## Quick Commands

Linux/macOS full bootstrap:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh
```

FreeBSD native bootstrap:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64
```

Windows bootstrap:

```bat
scripts\bootstrap\bootstrap-from-scratch.bat
```

QEMU FreeBSD bootstrap wrapper:

```bash
./scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --step=full2 --deploy
```

## Quick Commands

```bash
# C backend bootstrap (CMake + Ninja)
scripts/bootstrap/bootstrap-c.sh
scripts/bootstrap/bootstrap-c.sh --verify
```

## Script Map

- `scripts/bootstrap/bootstrap-c.sh`: C backend bootstrap (CMake + Ninja)
- `scripts/bootstrap/bootstrap-from-scratch.sh`: end-to-end bootstrap
- `scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64`: FreeBSD target flow
- `scripts/bootstrap/bootstrap-from-scratch.bat`: Windows flow
- `scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh`: QEMU FreeBSD environment wrapper

## Expected Output

- Final binary: `bin/release/simple`
- C backend bootstrap binary: `bin/bootstrap/cpp/simple`
- Intermediate artifacts: `build/bootstrap/`

## Related Docs

- `doc/build/bootstrap_pipeline.md`
- `doc/build/multiphase_bootstrap.md`
- `doc/guide/freebsd_qemu_bootstrap.md`
