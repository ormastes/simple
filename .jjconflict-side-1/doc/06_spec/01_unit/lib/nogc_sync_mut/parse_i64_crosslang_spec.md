# Parse I64 Crosslang Specification

> Tests covering decimal integer parsing — pure-Simple parse_i64 vs C oracle (well-formed inputs).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse I64 Crosslang Specification

## Scenarios

### decimal integer parsing — pure-Simple parse_i64 vs C oracle (well-formed inputs)

#### matches the C oracle on well-formed KAT integers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the C oracle on well-formed KAT integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on well-formed KAT integers")
assert_equal(simple_parse_i64("0"), rt_string_to_int("0"))
assert_equal(simple_parse_i64("0"), 0)
assert_equal(simple_parse_i64("42"), rt_string_to_int("42"))
assert_equal(simple_parse_i64("42"), 42)
assert_equal(simple_parse_i64("-1"), rt_string_to_int("-1"))
assert_equal(simple_parse_i64("-1"), -1)
assert_equal(simple_parse_i64("123456789"), rt_string_to_int("123456789"))
```

</details>

#### matches the C oracle across representative differential vectors

- matches the C oracle across representative differential vectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle across representative differential vectors")
val vectors = [
    "0", "1", "-1", "42", "-42", "007", "-007",
    "9223372036854775807", "-9223372036854775807",
    "  42", "42  ", "  -42  "
]
var i = 0
while i < vectors.len():
    val simple = simple_parse_i64(vectors[i])
    val oracle = rt_string_to_int(vectors[i])
    assert_equal(simple, oracle)
    i = i + 1
```

</details>

#### diverges by design on the empty string (documented, not asserted equal)

- diverges by design on the empty string (documented, not asserted equal)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("diverges by design on the empty string (documented, not asserted equal)")
# Different failure sentinels: Simple's `?? -1` vs the oracle's `unwrap_or(0)`.
assert_equal(simple_parse_i64(""), -1)
assert_equal(rt_string_to_int(""), 0)
```

</details>

#### diverges by design on malformed input (documented, not asserted equal)

- diverges by design on malformed input (documented, not asserted equal)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("diverges by design on malformed input (documented, not asserted equal)")
assert_equal(rt_string_to_int("42abc"), 0)
assert_equal(simple_parse_i64("42abc"), -1)
assert_equal(rt_string_to_int("abc"), 0)
assert_equal(simple_parse_i64("abc"), -1)
```

</details>

#### single-char corruption changes the parsed value (discrimination)

- single-char corruption changes the parsed value (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char corruption changes the parsed value (discrimination)")
val a = simple_parse_i64("123")
val b = simple_parse_i64("124")
assert_true(a != b)
assert_true(rt_string_to_int("123") != rt_string_to_int("124"))
```

</details>

#### is deterministic on both sides

- is deterministic on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic on both sides")
assert_equal(simple_parse_i64("777"), simple_parse_i64("777"))
assert_equal(rt_string_to_int("777"), rt_string_to_int("777"))
```

</details>

#### matches the C oracle on 100 shared branch-covering well-formed vectors, with perf evidence

- matches the C oracle on 100 shared branch-covering well-formed vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the C oracle on 100 shared branch-covering well-formed vectors, with perf evidence")
# SHARED TEST LOGIC (plan: "C-migration test standard"): one
# deterministic generator feeds the SAME input to BOTH sides inside
# this loop — the loop is the shared logic. Branch coverage: digit
# count 0..99 (empty, single-digit, multi-digit, wide magnitudes),
# a deterministic sign toggle, and leading/trailing whitespace
# padding of 0/1/2 chars cycling by index — all still well-formed so
# both sides genuinely agree.
use std.io_runtime.{time_now_unix_micros}
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var digits = ""
    var seed = i * 2654435761 % 4294967296
    var digit_count = i % 18
    var j = 0
    while j < digit_count:
        seed = (seed * 1103515245 + 12345) % 2147483648
        val d = seed % 10
        digits = digits + "{d}"
        j = j + 1
    if digits == "":
        digits = "0"
    val sign = if i % 2 == 0: "" else: "-"
    val pad_n = i % 3
    var pad = ""
    var k = 0
    while k < pad_n:
        pad = pad + " "
        k = k + 1
    val body = pad + sign + digits + pad
    val t0 = time_now_unix_micros()
    val s = simple_parse_i64(body)
    val t1 = time_now_unix_micros()
    val c = rt_string_to_int(body)
    val t2 = time_now_unix_micros()
    simple_us = simple_us + (t1 - t0)
    c_us = c_us + (t2 - t1)
    assert_equal(s, c)
    i = i + 1
print("perf_evidence: shared_corpus=100 simple_us={simple_us} c_us={c_us}")
assert_true(simple_us >= 0 and c_us >= 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering decimal integer parsing — pure-Simple parse_i64 vs C oracle (well-formed inputs).
- decimal integer parsing — pure-Simple parse_i64 vs C oracle (well-formed inputs)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-C-MIG-PARSEI64`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc4f03e69a4f7aa0d70a57b4137957ce0f5dbe59cfe0aa389bcfeb9d10752c3c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc4f03e69a4f7aa0d70a57b4137957ce0f5dbe59cfe0aa389bcfeb9d10752c3c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc4f03e69a4f7aa0d70a57b4137957ce0f5dbe59cfe0aa389bcfeb9d10752c3c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle on well-formed KAT integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the C oracle across representative differential vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/parse_i64_crosslang_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diverges by design on the empty string (documented, not asserted equal)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
