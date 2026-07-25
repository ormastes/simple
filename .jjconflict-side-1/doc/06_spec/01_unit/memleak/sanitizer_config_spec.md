# Sanitizer Config Specification

> <details>

<!-- sdn-diagram:id=sanitizer_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sanitizer_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sanitizer_config_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sanitizer_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sanitizer Config Specification

## Scenarios

### CMakeLists.txt has all sanitizer options

#### has ENABLE_UBSAN option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_UBSAN")).to_equal(true)
```

</details>

#### has ENABLE_TSAN option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_TSAN")).to_equal(true)
```

</details>

#### has ENABLE_MSAN option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_MSAN")).to_equal(true)
```

</details>

### CMakeLists.txt has mutual exclusion guard

#### has _SANITIZER_COUNT variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("_SANITIZER_COUNT")).to_equal(true)
```

</details>

#### has FATAL_ERROR for multiple sanitizers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("FATAL_ERROR")).to_equal(true)
```

</details>

### CMakeLists.txt has correct sanitizer flags

#### UBSan has -fno-sanitize-recover=undefined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-fno-sanitize-recover=undefined")).to_equal(true)
```

</details>

#### TSan has -fPIE flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-fPIE")).to_equal(true)
```

</details>

#### TSan has -pie link flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-pie")).to_equal(true)
```

</details>

#### MSan has -fsanitize-memory-track-origins=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-fsanitize-memory-track-origins=2")).to_equal(true)
```

</details>

### Suppression files exist and are non-empty

#### asan.supp exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/sanitizers/asan.supp") ?? ""
expect(content.len() > 0).to_equal(true)
```

</details>

#### lsan.supp exists with memtrack suppressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/sanitizers/lsan.supp") ?? ""
expect(content.contains("memtrack_ensure_init")).to_equal(true)
```

</details>

#### ubsan_blacklist.txt exists with ptr_hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/sanitizers/ubsan_blacklist.txt") ?? ""
expect(content.contains("ptr_hash")).to_equal(true)
```

</details>

#### tsan.supp exists with handle lock suppressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/sanitizers/tsan.supp") ?? ""
expect(content.contains("g_handle_lock_initialized")).to_equal(true)
```

</details>

### CI workflow sanitizer support (pending)

#### CMakeLists.txt has all three sanitizer options

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_UBSAN")).to_equal(true)
expect(content.contains("ENABLE_TSAN")).to_equal(true)
expect(content.contains("ENABLE_MSAN")).to_equal(true)
```

</details>

#### suppression files exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val asan = rt_file_read_text("src/compiler_cpp/sanitizers/asan.supp") ?? ""
val lsan = rt_file_read_text("src/compiler_cpp/sanitizers/lsan.supp") ?? ""
val tsan = rt_file_read_text("src/compiler_cpp/sanitizers/tsan.supp") ?? ""
expect(asan.len() > 0).to_equal(true)
expect(lsan.len() > 0).to_equal(true)
expect(tsan.len() > 0).to_equal(true)
```

</details>

#### ubsan blacklist exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/sanitizers/ubsan_blacklist.txt") ?? ""
expect(content.contains("ptr_hash")).to_equal(true)
```

</details>

#### has mutual exclusion guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("_SANITIZER_COUNT")).to_equal(true)
expect(content.contains("FATAL_ERROR")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Memory Safety |
| Status | Active |
| Source | `test/01_unit/memleak/sanitizer_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CMakeLists.txt has all sanitizer options
- CMakeLists.txt has mutual exclusion guard
- CMakeLists.txt has correct sanitizer flags
- Suppression files exist and are non-empty
- CI workflow sanitizer support (pending)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
