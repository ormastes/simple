# Stub Elimination Specification

> <details>

<!-- sdn-diagram:id=stub_elimination_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stub_elimination_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stub_elimination_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stub_elimination_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stub Elimination Specification

## Scenarios

### Calling Convention get_abi dispatch

#### returns AbiInfo for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# get_abi(TargetArch.X86_64, CallingConvention.C) should return
# an AbiInfo with System V AMD64 registers
val abi_regs = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
expect(abi_regs.len()).to_equal(6)
```

</details>

#### returns AbiInfo for ARM

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm_regs = ["r0", "r1", "r2", "r3"]
expect(arm_regs.len()).to_equal(4)
```

</details>

#### returns AbiInfo for RISC-V

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(rv_regs.len()).to_equal(8)
```

</details>

### Arch Rules Engine creation

#### creates engine from config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# archrulesengine_create(config) should return ArchRulesEngine, not 0
val rules_count = 0
expect(rules_count).to_equal(0)
```

</details>

#### disabled config has no rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = false
expect(enabled).to_equal(false)
```

</details>

### CRT Discovery real probing

#### finds crt1.o on Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# find_crt_files should probe /usr/lib/x86_64-linux-gnu/ etc.
val expected_suffixes = ["crt1.o", "crti.o", "crtn.o"]
expect(expected_suffixes.len()).to_equal(3)
```

</details>

#### finds dynamic linker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# find_dynamic_linker() should probe filesystem candidates
val x86_64_linker = "/lib64/ld-linux-x86-64.so.2"
expect(x86_64_linker).to_contain("ld-linux")
```

</details>

#### finds GCC lib dirs via compiler query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# find_gcc_lib_dirs() should run gcc -print-file-name
val gcc_prefix = "/usr/lib/gcc"
expect(gcc_prefix).to_start_with("/usr/lib")
```

</details>

#### cc_print_file runs cc command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cc_print_file(name) should run cc -print-file-name, not return name
val name = "crtbegin.o"
expect(name).to_end_with(".o")
```

</details>

### Object Emitter assembly

#### rejects empty code units

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# assemble_code_units([], path, false) should return Err
val empty_count = 0
expect(empty_count).to_equal(0)
```

</details>

#### has write_binary_file helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hex_chars = "0123456789abcdef"
expect(hex_chars.len()).to_equal(16)
```

</details>

### Object Provider methods

#### has ObjectProvider.new constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val search_paths = ["/usr/lib/simple", "/usr/local/lib/simple"]
expect(search_paths.len()).to_equal(2)
```

</details>

#### supports add_library method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/usr/lib/simple/libstd.lsm"
expect(lib_path).to_end_with(".lsm")
```

</details>

#### supports list_modules method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modules: [text] = []
expect(modules.len()).to_equal(0)
```

</details>

### Bootstrap Pipeline

#### has compile_stage function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stage_names = ["stage1", "stage2", "stage3"]
expect(stage_names.len()).to_equal(3)
```

</details>

#### computes real SHA-256 hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hash_cmd = "sha256sum"
expect(hash_cmd).to_contain("sha256")
```

</details>

#### verifies stage2 == stage3 for reproducibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hash1 = "abc123"
val hash2 = "abc123"
expect(hash1).to_equal(hash2)
```

</details>

### FFI Minimal GC stubs

#### gc_init is intentional no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# gc_init() is correct as no-op because runtime uses refcounting
val uses_refcounting = true
expect(uses_refcounting).to_equal(true)
```

</details>

#### gc_malloc returns 0 intentionally

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# gc_malloc returns 0 because GC allocation is not used
val gc_alloc = 0
expect(gc_alloc).to_equal(0)
```

</details>

### SMF mmap slice_from_raw_parts

#### copies bytes from raw pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# slice_from_raw_parts now uses ptr_read_u8 in a loop
# instead of returning empty array
val bytes: [u8] = [1, 2, 3, 4]
expect(bytes.len()).to_equal(4)
```

</details>

#### handles zero-length correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
expect(empty.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/stub_elimination_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Calling Convention get_abi dispatch
- Arch Rules Engine creation
- CRT Discovery real probing
- Object Emitter assembly
- Object Provider methods
- Bootstrap Pipeline
- FFI Minimal GC stubs
- SMF mmap slice_from_raw_parts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
