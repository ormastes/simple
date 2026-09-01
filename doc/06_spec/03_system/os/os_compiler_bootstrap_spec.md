# SimpleOS compiler and libc source contract — operator manual

Source: `test/03_system/os/os_compiler_bootstrap_spec.spl`

Status: source/manual current; pure-Simple Stage-4 execution, `spipe-docgen`,
and seven-score `sspec-maintain` evidence remain blocked by B-HOST-CLI.
Stubs: 0. Scenarios: 4 active, 0 skipped, 0 pending.

## Purpose and claim boundary

This `source-contract` spec preserves the useful inventory checks from the
historical bootstrap scenario while removing false acceptance signals. It
checks maintained libc, LLVM/Rust port, and SimpleOS integration owners. It
does not build or execute a compiler and cannot prove bootstrap convergence,
image admission, guest execution, or desktop readiness.

The spec deliberately does not check for the Rust seed, `bin/simple`, or the
Rust compiler target registry. Their presence is not pure-Simple self-host or
SimpleOS release evidence.

## Preconditions

- Run from the repository root with an admitted pure-Simple Stage-4 runner.
- The source checkout is complete; generated build output is not required.
- Treat a green result only as source-layout evidence.

## Operator workflow

1. Run the executable SSpec once with the admitted runner.
2. Require all four examples to execute and exit zero.
3. If a path moved intentionally, update its production owner and this source
   contract together; do not add an alternate compatibility copy.
4. Retain the spec and runner SHA-256 plus stdout/stderr.
5. Generate the manual with `0 stubs` and inspect all seven `sspec-maintain`
   scores when Stage 4 is available.

## Scenarios

### SimpleOS compiler and libc source contract

#### should retain the libc build and header surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should retain the libc build and header surface
- Inspect the maintained SimpleOS libc build and headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the libc build and header surface")
step("Inspect the maintained SimpleOS libc build and headers")
expect(all_files_exist([
    "src/os/libc/Makefile",
    "src/os/libc/include/stdio.h",
    "src/os/libc/include/stdlib.h",
    "src/os/libc/include/string.h",
    "src/os/libc/include/setjmp.h",
    "src/os/libc/include/pthread.h",
    "src/os/libc/include/math.h",
    "src/os/libc/include/errno.h",
])).to_be(true)
```

</details>

#### should retain the libc implementation surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has = file_exists("src/os/libc/include/stdlib.h")
expect(has).to_equal(true)
```

</details>

#### sysroot includes string.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/libc/include/string.h")).to_equal(true)
```

</details>

#### sysroot includes setjmp.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/libc/include/setjmp.h")).to_equal(true)
```

</details>

#### sysroot includes pthread.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/libc/include/pthread.h")).to_equal(true)
```

</details>

#### sysroot includes math.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/libc/include/math.h")).to_equal(true)
```

</details>

#### sysroot includes errno.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/libc/include/errno.h")).to_equal(true)
```

</details>

#### libc source files are complete (14 .c files)

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "src/os/libc/simpleos_libc.c",
    "src/os/libc/simpleos_math.c",
    "src/os/libc/simpleos_math_ext.c",
    "src/os/libc/simpleos_fs.c",
    "src/os/libc/simpleos_process.c",
    "src/os/libc/simpleos_pthread.c",
    "src/os/libc/simpleos_alloc.c",
    "src/os/libc/simpleos_string_ext.c",
    "src/os/libc/simpleos_stdlib_ext.c",
    "src/os/libc/simpleos_time.c",
    "src/os/libc/simpleos_printf_float.c",
    "src/os/libc/simpleos_cxxabi.c",
    "src/os/libc/simpleos_dlmalloc.c",
    "src/os/libc/simpleos_signal.c"
]
var all_exist = true
for f in files:
    if not file_exists(f):
        all_exist = false
expect(all_exist).to_equal(true)
```

</details>

### Tier 6 — LLVM Cross-Build

#### LLVM build script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/llvm/build.shs")).to_equal(true)
```

</details>

#### LLVM sysroot script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/llvm/sysroot.shs")).to_equal(true)
```

</details>

#### LLVM build config exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/llvm/build.spl")).to_equal(true)
```

</details>

#### CMake toolchain exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/toolchain/llvm/simpleos_cross_toolchain.cmake")).to_equal(true)
```

</details>

#### LLVM smoke test exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/llvm/test_smoke.spl")).to_equal(true)
```

</details>

### Tier 6 — Rust Cross-Build

#### Rust target spec exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/toolchain/rust/x86_64-unknown-simpleos.json")).to_equal(true)
```

</details>

#### Rust build script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/rust/build.shs")).to_equal(true)
```

</details>

#### Rust build config exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/rust/build.spl")).to_equal(true)
```

</details>

#### Rust cargo config exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/toolchain/rust/cargo_config.toml")).to_equal(true)
```

</details>

#### Rust hello example exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/rust/examples/hello.rs")).to_equal(true)
```

</details>

#### Rust IPC sample exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/rust/examples/ipc_sample.rs")).to_equal(true)
```

</details>

### Tier 7 — Simple Compiler Bootstrap

#### Rust seed Cargo.toml exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler_rust/Cargo.toml")).to_equal(true)
```

</details>

#### bootstrap script exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("scripts/bootstrap/bootstrap-from-scratch.sh")).to_equal(true)
```

</details>

#### Canonical SimpleOS deployment desktop toolchain spec exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl")).to_equal(true)
```

</details>

#### bin/simple exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("bin/simple")).to_equal(true)
```

</details>

#### SimpleOS target is defined in compiler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target_file = "src/compiler_rust/common/src/target.rs"
expect(file_exists(target_file)).to_equal(true)
```

</details>

#### native build config for SimpleOS exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/simpleos_native_build_config.spl")).to_equal(true)
```

</details>

#### Simple make build tool exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/port/build_tools/simple_make.spl")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_compiler_bootstrap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Compiler Toolchain Bootstrap
- Tier 6 — Sysroot and Libc
- Tier 6 — LLVM Cross-Build
- Tier 6 — Rust Cross-Build
- Tier 7 — Simple Compiler Bootstrap

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
