# Sanitizer Specification

> <details>

<!-- sdn-diagram:id=sanitizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sanitizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sanitizer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sanitizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sanitizer Specification

## Scenarios

### Sanitizer

#### keeps shared sanitizer event type available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = sanitizer_source("types.spl")

expect(source).to_contain("struct SanEvent:")
expect(source).to_contain("kind: text")
expect(source).to_contain("severity: text")
expect(source).to_contain("message: text")
expect(source).to_contain("location: text")
expect(source).to_contain("fn san_event(kind: text, severity: text, message: text, location: text) -> SanEvent")
```

</details>

#### keeps unified sanitizer API wiring available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = sanitizer_source("mod.spl")

expect(source).to_contain("fn san_enable_all()")
expect(source).to_contain("fn san_disable_all()")
expect(source).to_contain("fn san_report_all()")
expect(source).to_contain("fn san_reset_all()")
expect(source).to_contain("fn san_total_errors() -> i64")
expect(source).to_contain("asan_error_count() + lsan_error_count() + ubsan_error_count() + tsan_error_count() + msan_error_count()")
```

</details>

#### keeps ASan allocation and access checks available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = sanitizer_source("asan/mod.spl")

expect(source).to_contain("var g_asan_enabled: bool = false")
expect(source).to_contain("fn asan_enable()")
expect(source).to_contain("fn asan_on_alloc(id: i64, size: i64, tag: text)")
expect(source).to_contain("fn asan_on_free(id: i64)")
expect(source).to_contain("fn asan_check_access(id: i64) -> bool")
expect(source).to_contain("fn asan_check_bounds(id: i64, offset: i64, access_size: i64) -> bool")
expect(source).to_contain("use-after-free")
expect(source).to_contain("buffer overflow")
```

</details>

#### keeps leak and undefined behavior sanitizer checks available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lsan = sanitizer_source("lsan/mod.spl")
val ubsan = sanitizer_source("ubsan/mod.spl")

expect(lsan).to_contain("fn lsan_checkpoint(name: text)")
expect(lsan).to_contain("fn lsan_check_since(name: text) -> i64")
expect(lsan).to_contain("fn lsan_suppress_tag(tag: text)")
expect(ubsan).to_contain("fn ubsan_check_not_nil(value: i64, context: text) -> bool")
expect(ubsan).to_contain("fn ubsan_add_i64(a: i64, b: i64) -> i64")
expect(ubsan).to_contain("fn ubsan_div_i64(a: i64, b: i64) -> i64")
expect(ubsan).to_contain("fn ubsan_check_index(arr_len: i64, idx: i64) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/sanitizer/sanitizer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Sanitizer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
