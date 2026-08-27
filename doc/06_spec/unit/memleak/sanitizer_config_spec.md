# Sanitizer Config Specification

> Tests covering CMakeLists.txt has all sanitizer options, CMakeLists.txt has mutual exclusion guard, CMakeLists.txt has correct sanitizer flags, Suppression files exist and are non-empty, CI workflow sanitizer support (pending).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sanitizer Config Specification

## Scenarios

### CMakeLists.txt has all sanitizer options

#### has ENABLE_UBSAN option

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has ENABLE_UBSAN option
   - Expected: content contains `ENABLE_UBSAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has ENABLE_UBSAN option")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_UBSAN")).to_equal(true)
```

</details>

#### has ENABLE_TSAN option

- has ENABLE_TSAN option
   - Expected: content contains `ENABLE_TSAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has ENABLE_TSAN option")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_TSAN")).to_equal(true)
```

</details>

#### has ENABLE_MSAN option

- has ENABLE_MSAN option
   - Expected: content contains `ENABLE_MSAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has ENABLE_MSAN option")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_MSAN")).to_equal(true)
```

</details>

### CMakeLists.txt has mutual exclusion guard

#### has _SANITIZER_COUNT variable

- has _SANITIZER_COUNT variable
   - Expected: content contains `_SANITIZER_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has _SANITIZER_COUNT variable")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("_SANITIZER_COUNT")).to_equal(true)
```

</details>

#### has FATAL_ERROR for multiple sanitizers

- has FATAL_ERROR for multiple sanitizers
   - Expected: content contains `FATAL_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has FATAL_ERROR for multiple sanitizers")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("FATAL_ERROR")).to_equal(true)
```

</details>

### CMakeLists.txt has correct sanitizer flags

#### UBSan has -fno-sanitize-recover=undefined

- UBSan has -fno-sanitize-recover=undefined
   - Expected: content contains `-fno-sanitize-recover=undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UBSan has -fno-sanitize-recover=undefined")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-fno-sanitize-recover=undefined")).to_equal(true)
```

</details>

#### TSan has -fPIE flag

- TSan has -fPIE flag
   - Expected: content contains `-fPIE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TSan has -fPIE flag")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-fPIE")).to_equal(true)
```

</details>

#### TSan has -pie link flag

- TSan has -pie link flag
   - Expected: content contains `-pie`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TSan has -pie link flag")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-pie")).to_equal(true)
```

</details>

#### MSan has -fsanitize-memory-track-origins=2

- MSan has -fsanitize-memory-track-origins=2
   - Expected: content contains `-fsanitize-memory-track-origins=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MSan has -fsanitize-memory-track-origins=2")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("-fsanitize-memory-track-origins=2")).to_equal(true)
```

</details>

### Suppression files exist and are non-empty

#### asan.supp exists

- asan.supp exists
   - Expected: content.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("asan.supp exists")
val content = rt_file_read_text("src/compiler_cpp/sanitizers/asan.supp") ?? ""
expect(content.len() > 0).to_equal(true)
```

</details>

#### lsan.supp exists with memtrack suppressions

- lsan.supp exists with memtrack suppressions
   - Expected: content contains `memtrack_ensure_init`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lsan.supp exists with memtrack suppressions")
val content = rt_file_read_text("src/compiler_cpp/sanitizers/lsan.supp") ?? ""
expect(content.contains("memtrack_ensure_init")).to_equal(true)
```

</details>

#### ubsan_blacklist.txt exists with ptr_hash

- ubsan_blacklist.txt exists with ptr_hash
   - Expected: content contains `ptr_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ubsan_blacklist.txt exists with ptr_hash")
val content = rt_file_read_text("src/compiler_cpp/sanitizers/ubsan_blacklist.txt") ?? ""
expect(content.contains("ptr_hash")).to_equal(true)
```

</details>

#### tsan.supp exists with handle lock suppressions

- tsan.supp exists with handle lock suppressions
   - Expected: content contains `g_handle_lock_initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tsan.supp exists with handle lock suppressions")
val content = rt_file_read_text("src/compiler_cpp/sanitizers/tsan.supp") ?? ""
expect(content.contains("g_handle_lock_initialized")).to_equal(true)
```

</details>

### CI workflow sanitizer support (pending)

#### CMakeLists.txt has all three sanitizer options

- CMakeLists.txt has all three sanitizer options
   - Expected: content contains `ENABLE_UBSAN`
   - Expected: content contains `ENABLE_TSAN`
   - Expected: content contains `ENABLE_MSAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CMakeLists.txt has all three sanitizer options")
val content = rt_file_read_text("src/compiler_cpp/CMakeLists.txt") ?? ""
expect(content.contains("ENABLE_UBSAN")).to_equal(true)
expect(content.contains("ENABLE_TSAN")).to_equal(true)
expect(content.contains("ENABLE_MSAN")).to_equal(true)
```

</details>

#### suppression files exist

- suppression files exist
   - Expected: asan.len() > 0 is true
   - Expected: lsan.len() > 0 is true
   - Expected: tsan.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suppression files exist")
val asan = rt_file_read_text("src/compiler_cpp/sanitizers/asan.supp") ?? ""
val lsan = rt_file_read_text("src/compiler_cpp/sanitizers/lsan.supp") ?? ""
val tsan = rt_file_read_text("src/compiler_cpp/sanitizers/tsan.supp") ?? ""
expect(asan.len() > 0).to_equal(true)
expect(lsan.len() > 0).to_equal(true)
expect(tsan.len() > 0).to_equal(true)
```

</details>

#### ubsan blacklist exists

- ubsan blacklist exists
   - Expected: content contains `ptr_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ubsan blacklist exists")
val content = rt_file_read_text("src/compiler_cpp/sanitizers/ubsan_blacklist.txt") ?? ""
expect(content.contains("ptr_hash")).to_equal(true)
```

</details>

#### has mutual exclusion guard

- has mutual exclusion guard
   - Expected: content contains `_SANITIZER_COUNT`
   - Expected: content contains `FATAL_ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has mutual exclusion guard")
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
| Source | `test/unit/memleak/sanitizer_config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CMakeLists.txt has all sanitizer options, CMakeLists.txt has mutual exclusion guard, CMakeLists.txt has correct sanitizer flags, Suppression files exist and are non-empty, CI workflow sanitizer support (pending).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `579bff62fa568504acef12ce845fc02efa7526240ea17bc6ed88162b27efe5b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `579bff62fa568504acef12ce845fc02efa7526240ea17bc6ed88162b27efe5b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `579bff62fa568504acef12ce845fc02efa7526240ea17bc6ed88162b27efe5b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/memleak/sanitizer_config_spec.spl
mirror: doc/06_spec/unit/memleak/sanitizer_config_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/memleak/sanitizer_config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/memleak/sanitizer_config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/memleak/sanitizer_config_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has ENABLE_UBSAN option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/sanitizer_config_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has ENABLE_TSAN option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/memleak/sanitizer_config_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has ENABLE_MSAN option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
