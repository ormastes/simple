# Sanitizer Specification

> Tests covering Sanitizer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sanitizer Specification

## Scenarios

### Sanitizer

#### keeps shared sanitizer event type available

- keeps shared sanitizer event type available


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps shared sanitizer event type available")
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

- keeps unified sanitizer API wiring available


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps unified sanitizer API wiring available")
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

- keeps ASan allocation and access checks available


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ASan allocation and access checks available")
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

- keeps leak and undefined behavior sanitizer checks available


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps leak and undefined behavior sanitizer checks available")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Sanitizer.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3231d0962b301501517de637073bd37c9811673766815cfa40cc9271587b333f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3231d0962b301501517de637073bd37c9811673766815cfa40cc9271587b333f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3231d0962b301501517de637073bd37c9811673766815cfa40cc9271587b333f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/sanitizer/sanitizer_spec.spl
mirror: doc/06_spec/01_unit/lib/sanitizer/sanitizer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/sanitizer/sanitizer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/sanitizer/sanitizer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/sanitizer/sanitizer_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps shared sanitizer event type available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/sanitizer/sanitizer_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps unified sanitizer API wiring available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/sanitizer/sanitizer_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps ASan allocation and access checks available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
