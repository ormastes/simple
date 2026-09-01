# Dual Run Shadow Specification

> Tests covering dual_run shadow harness — C oracle vs Simple, 4 migrated pairs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dual Run Shadow Specification

## Scenarios

### dual_run shadow harness — C oracle vs Simple, 4 migrated pairs

#### floor_f64 vs rt_math_floor agrees on representative + edge inputs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- floor_f64 vs rt_math_floor agrees on representative + edge inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("floor_f64 vs rt_math_floor agrees on representative + edge inputs")
# bit_exact: false here (plain `==`) -- matches the convention of
# the existing floor_f64 crosslang spec's assert_equal. Sign-of-zero
# on -0.0 differs between bin/simple test's tree-walk interpreter
# and bin/simple run's JIT for this pair (a real, already-known
# run-vs-test engine divergence class per .claude/rules/testing.md,
# not a floor_f64 defect); bit_exact:true would flag it, which is
# exactly what the sanity checks below demonstrate on purpose.
val xs = [3.0, 3.7, -3.1, 0.0, -0.0, 1.0e20, 0.0 - 1.0e20]
var i = 0
var checked = 0
while i < xs.len():
    val x = xs[i]
    val v = dual_check_f64("floor_f64", floor_f64(x), rt_math_floor(x), false)
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
# NaN case: both-NaN must count as agreement, not divergence.
val big = 1.0e308
val pos_inf = big * 10.0
val nan_x = pos_inf - pos_inf
val nan_v = dual_check_f64("floor_f64_nan", floor_f64(nan_x), rt_math_floor(nan_x), false)
assert_true(nan_v.agree)
assert_equal(checked, 7)
```

</details>

#### ceil_f64 vs rt_math_ceil agrees on representative + edge inputs

- ceil_f64 vs rt_math_ceil agrees on representative + edge inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ceil_f64 vs rt_math_ceil agrees on representative + edge inputs")
val xs = [3.0, 3.2, -3.1, 0.0, -0.5, 1.0e20, 0.0 - 1.0e20]
var i = 0
var checked = 0
while i < xs.len():
    val x = xs[i]
    val v = dual_check_f64("ceil_f64", ceil_f64(x), rt_math_ceil(x), false)
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 7)
```

</details>

#### i64_to_text vs rt_raw_i64_to_string agrees on boundary + typical values

- i64_to_text vs rt_raw_i64_to_string agrees on boundary + typical values


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("i64_to_text vs rt_raw_i64_to_string agrees on boundary + typical values")
val ns = [0, 1, -1, 42, -42, 9223372036854775807, -9223372036854775808]
var i = 0
var checked = 0
while i < ns.len():
    val n = ns[i]
    val v = dual_check_text("i64_to_text", i64_to_text(n), rt_raw_i64_to_string(n))
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 7)
```

</details>

#### byte_char vs rt_byte_char agrees across the full 0..255 byte range

- byte_char vs rt_byte_char agrees across the full 0..255 byte range


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("byte_char vs rt_byte_char agrees across the full 0..255 byte range")
var b = 0
var checked = 0
var divergent = 0
while b < 256:
    val v = dual_check_text("byte_char", byte_char(b), rt_byte_char(b))
    if not v.agree:
        divergent = divergent + 1
    checked = checked + 1
    b = b + 1
assert_equal(divergent, 0)
assert_equal(checked, 256)
```

</details>

#### dual_check_f64 detects a deliberately divergent pair (sanity: the helper is not vacuous)

- dual_check_f64 detects a deliberately divergent pair (sanity: the helper is not vacuous)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dual_check_f64 detects a deliberately divergent pair (sanity: the helper is not vacuous)")
val v = dual_check_f64("deliberately_wrong", 1.0, 2.0, false)
assert_true(not v.agree)
```

</details>

#### dual_check_text detects a deliberately divergent pair (sanity: the helper is not vacuous)

- dual_check_text detects a deliberately divergent pair (sanity: the helper is not vacuous)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dual_check_text detects a deliberately divergent pair (sanity: the helper is not vacuous)")
val v = dual_check_text("deliberately_wrong_text", "a", "b")
assert_true(not v.agree)
```

</details>

#### dual_check_f64 bit_exact:true distinguishes -0.0 from 0.0, unlike plain ==

- dual_check_f64 bit_exact:true distinguishes -0.0 from 0.0, unlike plain ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dual_check_f64 bit_exact:true distinguishes -0.0 from 0.0, unlike plain ==")
val loose = dual_check_f64("zero_loose", 0.0, -0.0, false)
assert_true(loose.agree)
val strict = dual_check_f64("zero_strict", 0.0, -0.0, true)
assert_true(not strict.agree)
```

</details>

#### dual_check_f64 treats both-NaN as agreement (NaN-safe), not a divergence

- dual_check_f64 treats both-NaN as agreement (NaN-safe), not a divergence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dual_check_f64 treats both-NaN as agreement (NaN-safe), not a divergence")
val big = 1.0e308
val pos_inf = big * 10.0
val nan_a = pos_inf - pos_inf
val nan_b = pos_inf - pos_inf
val v = dual_check_f64("nan_pair", nan_a, nan_b, false)
assert_true(v.agree)
```

</details>

#### timestamp_from_components vs rt_timestamp_from_components agrees on epoch/leap/century/pre-epoch vectors

- timestamp_from_components vs rt_timestamp_from_components agrees on epoch/leap/century/pre-epoch vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("timestamp_from_components vs rt_timestamp_from_components agrees on epoch/leap/century/pre-epoch vectors")
# year, month, day, hour, minute, second, microsecond
val vectors = [
    (1970, 1, 1, 0, 0, 0, 0),
    (2000, 2, 29, 0, 0, 0, 0),        # 400-year leap day
    (1900, 2, 28, 23, 59, 59, 999999), # century non-leap boundary
    (2038, 1, 19, 3, 14, 8, 0),        # 32-bit rollover
    (1969, 12, 31, 23, 59, 59, 0),     # pre-epoch
    (2024, 12, 31, 23, 59, 59, 500000),
]
var i = 0
var checked = 0
while i < vectors.len():
    val (y, mo, d, h, mi, se, us) = vectors[i]
    val simple = timestamp_from_components(y, mo, d, h, mi, se, us)
    val oracle = rt_timestamp_from_components(y as i32, mo as i32, d as i32, h as i32, mi as i32, se as i32, us as i32)
    val v = dual_check_text("timestamp_from_components", "{simple}", "{oracle}")
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 6)
```

</details>

#### timestamp_add_days vs rt_timestamp_add_days agrees on positive/negative/zero offsets

- timestamp_add_days vs rt_timestamp_add_days agrees on positive/negative/zero offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("timestamp_add_days vs rt_timestamp_add_days agrees on positive/negative/zero offsets")
val base = timestamp_from_components(2024, 6, 15, 12, 0, 0, 0)
val offsets = [0, 1, -1, 30, -365, 146097]  # 146097 days = 400 years
var i = 0
var checked = 0
while i < offsets.len():
    val simple = timestamp_add_days(base, offsets[i])
    val oracle = rt_timestamp_add_days(base, offsets[i])
    val v = dual_check_text("timestamp_add_days", "{simple}", "{oracle}")
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 6)
```

</details>

#### timestamp_diff_days vs rt_timestamp_diff_days agrees, incl. negative diffs

- timestamp_diff_days vs rt_timestamp_diff_days agrees, incl. negative diffs


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("timestamp_diff_days vs rt_timestamp_diff_days agrees, incl. negative diffs")
val a = timestamp_from_components(2024, 6, 15, 0, 0, 0, 0)
val b = timestamp_from_components(2024, 1, 1, 0, 0, 0, 0)
val c = timestamp_from_components(1969, 12, 1, 0, 0, 0, 0)
val pairs = [(a, b), (b, a), (a, a), (a, c), (c, a)]
var i = 0
var checked = 0
while i < pairs.len():
    val (m1, m2) = pairs[i]
    val simple = timestamp_diff_days(m1, m2)
    val oracle = rt_timestamp_diff_days(m1, m2)
    val v = dual_check_text("timestamp_diff_days", "{simple}", "{oracle}")
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 5)
```

</details>

#### timestamp_get_year/month/day vs rt_timestamp_get_year/month/day agree on boundary timestamps

- timestamp_get_year/month/day vs rt_timestamp_get_year/month/day agree on boundary timestamps


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("timestamp_get_year/month/day vs rt_timestamp_get_year/month/day agree on boundary timestamps")
val micros_list = [
    timestamp_from_components(1970, 1, 1, 0, 0, 0, 0),
    timestamp_from_components(2000, 2, 29, 0, 0, 0, 0),
    timestamp_from_components(1900, 2, 28, 0, 0, 0, 0),
    timestamp_from_components(2038, 1, 19, 3, 14, 8, 0),
    timestamp_from_components(1969, 12, 31, 23, 59, 59, 0),
]
var i = 0
var checked = 0
while i < micros_list.len():
    val m = micros_list[i]
    val y_v = dual_check_text("timestamp_get_year", "{timestamp_get_year(m)}", "{rt_timestamp_get_year(m)}")
    val mo_v = dual_check_text("timestamp_get_month", "{timestamp_get_month(m)}", "{rt_timestamp_get_month(m)}")
    val d_v = dual_check_text("timestamp_get_day", "{timestamp_get_day(m)}", "{rt_timestamp_get_day(m)}")
    assert_true(y_v.agree)
    assert_true(mo_v.agree)
    assert_true(d_v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 5)
```

</details>

#### rt_hash_text (Simple FNV-1a bridge) vs C oracle rt_hash_text agrees incl. UTF-8

- rt_hash_text (Simple FNV-1a bridge) vs C oracle rt_hash_text agrees incl. UTF-8


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rt_hash_text (Simple FNV-1a bridge) vs C oracle rt_hash_text agrees incl. UTF-8")
val vectors = ["", "a", "abc", "hello world", "héllo", "日本語", "emoji 🎉 test", "Ω≈ç√∫"]
var i = 0
var checked = 0
while i < vectors.len():
    val simple = simple_hash_text(vectors[i])
    val oracle = rt_hash_text(vectors[i])
    val v = dual_check_text("rt_hash_text", "{simple}", "{oracle}")
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 8)
```

</details>

#### parse_i64 vs rt_string_to_int agrees on well-formed decimal integers (sentinel divergence documented, not asserted)

- parse_i64 vs rt_string_to_int agrees on well-formed decimal integers (sentinel divergence documented, not asserted)


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parse_i64 vs rt_string_to_int agrees on well-formed decimal integers (sentinel divergence documented, not asserted)")
# NOTE: on malformed/empty input the two sides use DIFFERENT sentinels
# (parse_i64 -1 vs rt_string_to_int 0 per C-MIG-0021's caller_note) —
# this pair intentionally restricts to well-formed input, matching
# test/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.spl's convention.
val vectors = ["0", "1", "-1", "42", "-42", "9223372036854775807", "-9223372036854775808"]
var i = 0
var checked = 0
while i < vectors.len():
    val simple = parse_i64(vectors[i])
    val oracle = rt_string_to_int(vectors[i])
    val v = dual_check_text("parse_i64", "{simple}", "{oracle}")
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 7)
```

</details>

#### validated_utf8_bytes_to_text_linear vs rt_text_validate_utf8 agrees on valid/invalid UTF-8, incl. multibyte

- validated_utf8_bytes_to_text_linear vs rt_text_validate_utf8 agrees on valid/invalid UTF-8, incl. multibyte


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validated_utf8_bytes_to_text_linear vs rt_text_validate_utf8 agrees on valid/invalid UTF-8, incl. multibyte")
val vectors = ["", "a", "hello world", "héllo", "日本語ABCabc", "emoji 🎉 TEST", "Ω≈ç√∫ mixedCase", "Café", "naïve", "東京", "👍👎🎉"]
var i = 0
var checked = 0
while i < vectors.len():
    val simple = bool_text(simple_is_valid_utf8(vectors[i]))
    val oracle = bool_text(rt_text_validate_utf8(vectors[i]))
    val v = dual_check_text("utf8_validate", simple, oracle)
    assert_true(v.agree)
    checked = checked + 1
    i = i + 1
assert_equal(checked, 11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/dual_run_shadow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dual_run shadow harness — C oracle vs Simple, 4 migrated pairs.
- dual_run shadow harness — C oracle vs Simple, 4 migrated pairs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-DUAL-RUN-SHADOW`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dce83784bce6559ca6913af24bac2e09661b8c6e5f29c98295f993dfd4e6d88d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dce83784bce6559ca6913af24bac2e09661b8c6e5f29c98295f993dfd4e6d88d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dce83784bce6559ca6913af24bac2e09661b8c6e5f29c98295f993dfd4e6d88d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/spec/dual_run_shadow_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/dual_run_shadow_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/spec/dual_run_shadow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/dual_run_shadow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/dual_run_shadow_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/spec/dual_run_shadow_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'floor_f64 vs rt_math_floor agrees on representative + edge inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/dual_run_shadow_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ceil_f64 vs rt_math_ceil agrees on representative + edge inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/dual_run_shadow_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i64_to_text vs rt_raw_i64_to_string agrees on boundary + typical values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
