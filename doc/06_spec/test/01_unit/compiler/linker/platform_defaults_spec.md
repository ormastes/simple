# Platform Defaults Specification

> <details>

<!-- sdn-diagram:id=platform_defaults_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=platform_defaults_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

platform_defaults_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=platform_defaults_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Defaults Specification

## Scenarios

### platform_defaults

### default_libraries

#### linux_libs: Linux has c, pthread, dl, m

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_default_libraries("linux")
expect(libs.len()).to_equal(4)
expect(libs[0]).to_equal("c")
expect(libs[1]).to_equal("pthread")
expect(libs[2]).to_equal("dl")
expect(libs[3]).to_equal("m")
```

</details>

#### macos_libs: macOS has c, pthread, m, System

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_default_libraries("macos")
expect(libs.len()).to_equal(4)
expect(libs[0]).to_equal("c")
expect(libs[3]).to_equal("System")
```

</details>

#### darwin_libs: Darwin alias works like macos

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_default_libraries("Darwin")
expect(libs.len()).to_equal(4)
expect(libs[3]).to_equal("System")
```

</details>

#### freebsd_libs: FreeBSD has c, pthread, m

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_default_libraries("freebsd")
expect(libs.len()).to_equal(3)
expect(libs[0]).to_equal("c")
```

</details>

#### windows_libs: Windows has kernel32, user32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_default_libraries("windows")
expect(libs.len()).to_equal(2)
expect(libs[0]).to_equal("kernel32")
expect(libs[1]).to_equal("user32")
```

</details>

#### unknown_os_libs: unknown OS returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_default_libraries("haiku")
expect(libs.len()).to_equal(0)
```

</details>

### default_library_dirs

#### unix_lib_dirs: Unix OSes get simple lib dirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_library_dirs("linux")
expect(dirs.len()).to_equal(2)
expect(dirs[0]).to_equal("/usr/lib/simple")
expect(dirs[1]).to_equal("/usr/local/lib/simple")
```

</details>

#### windows_lib_dirs: Windows gets empty lib dirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_library_dirs("windows")
expect(dirs.len()).to_equal(0)
```

</details>

### crt_search_dirs

#### x86_64_crt: x86_64 has 4 search dirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_crt_search_dirs("linux", "x86_64")
expect(dirs.len()).to_equal(4)
expect(dirs[0]).to_equal("/usr/lib/x86_64-linux-gnu")
```

</details>

#### aarch64_crt: aarch64 has 3 search dirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_crt_search_dirs("linux", "aarch64")
expect(dirs.len()).to_equal(3)
expect(dirs[0]).to_equal("/usr/lib/aarch64-linux-gnu")
```

</details>

#### riscv64_crt: riscv64 has 3 search dirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_crt_search_dirs("linux", "riscv64")
expect(dirs.len()).to_equal(3)
```

</details>

#### unknown_arch_crt: unknown arch falls back to /usr/lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_crt_search_dirs("linux", "mips")
expect(dirs.len()).to_equal(1)
expect(dirs[0]).to_equal("/usr/lib")
```

</details>

#### non_linux_crt: non-Linux gets empty CRT dirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_crt_search_dirs("macos", "x86_64")
expect(dirs.len()).to_equal(0)
```

</details>

### dynamic_linker_candidates

#### linux_x86_64_dynlinker: x86_64 has 3 candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = helper_default_dynamic_linker_candidates("linux", "x86_64")
expect(candidates.len()).to_equal(3)
expect(candidates[0]).to_equal("/lib64/ld-linux-x86-64.so.2")
```

</details>

#### linux_aarch64_dynlinker: aarch64 has 2 candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = helper_default_dynamic_linker_candidates("linux", "aarch64")
expect(candidates.len()).to_equal(2)
```

</details>

#### linux_riscv64_dynlinker: riscv64 has 2 candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = helper_default_dynamic_linker_candidates("linux", "riscv64")
expect(candidates.len()).to_equal(2)
```

</details>

#### freebsd_dynlinker: FreeBSD has 1 candidate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = helper_default_dynamic_linker_candidates("freebsd", "x86_64")
expect(candidates.len()).to_equal(1)
expect(candidates[0]).to_equal("/libexec/ld-elf.so.1")
```

</details>

#### unknown_os_dynlinker: unknown OS returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = helper_default_dynamic_linker_candidates("windows", "x86_64")
expect(candidates.len()).to_equal(0)
```

</details>

### elf_emulation

#### x86_64_emulation: x86_64 returns elf_x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_elf_emulation("x86_64")).to_equal("elf_x86_64")
```

</details>

#### aarch64_emulation: aarch64 returns aarch64linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_elf_emulation("aarch64")).to_equal("aarch64linux")
```

</details>

#### riscv64_emulation: riscv64 returns elf64lriscv

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_elf_emulation("riscv64")).to_equal("elf64lriscv")
```

</details>

#### i686_emulation: i686 returns elf_i386

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_elf_emulation("i686")).to_equal("elf_i386")
```

</details>

#### unknown_emulation: unknown arch returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_elf_emulation("mips")).to_equal("")
```

</details>

### gcc_triplet

#### x86_64_triplet: x86_64 returns x86_64-linux-gnu

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_gcc_triplet("x86_64")).to_equal("x86_64-linux-gnu")
```

</details>

#### aarch64_triplet: aarch64 returns aarch64-linux-gnu

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_gcc_triplet("aarch64")).to_equal("aarch64-linux-gnu")
```

</details>

#### riscv64_triplet: riscv64 returns riscv64-linux-gnu

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_gcc_triplet("riscv64")).to_equal("riscv64-linux-gnu")
```

</details>

#### unknown_triplet: unknown arch defaults to x86_64-linux-gnu

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_gcc_triplet("mips")).to_equal("x86_64-linux-gnu")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/platform_defaults_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- platform_defaults
- default_libraries
- default_library_dirs
- crt_search_dirs
- dynamic_linker_candidates
- elf_emulation
- gcc_triplet

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
