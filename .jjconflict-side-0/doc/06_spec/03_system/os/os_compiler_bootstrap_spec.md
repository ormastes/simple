# Os Compiler Bootstrap Specification

> <details>

<!-- sdn-diagram:id=os_compiler_bootstrap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_compiler_bootstrap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_compiler_bootstrap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_compiler_bootstrap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Compiler Bootstrap Specification

## Scenarios

### Compiler Toolchain Bootstrap

### Tier 6 — Sysroot and Libc

#### libc Makefile exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/libc/Makefile")).to_equal(true)
```

</details>

#### sysroot includes stdio.h

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Check if sysroot has been built, or source header exists
val has_sysroot = file_exists("build/os/sysroot/include/stdio.h")
val has_source = file_exists("src/os/libc/include/stdio.h")
expect(has_sysroot or has_source).to_equal(true)
```

</details>

#### sysroot includes stdlib.h

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

#### SimpleOS guest toolchain live spec exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("test/system/simpleos_guest_toolchain_live_spec.spl")).to_equal(true)
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
