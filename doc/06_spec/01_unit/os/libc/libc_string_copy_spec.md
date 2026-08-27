# Libc String Copy Specification

> Tests covering SimpleOS libc — string copy/concat functions, strcpy, strncpy, strcat, strncat, strdup, strndup, strnlen, strlcpy, strlcat.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Libc String Copy Specification

## Scenarios

### SimpleOS libc — string copy/concat functions

### strcpy

#### copies a non-empty string

- copies a non-empty string
   - Expected: dst.len() equals `5`
   - Expected: dst[0] equals `104`
   - Expected: dst[4] equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("copies a non-empty string")
val src = "hello".bytes()
val dst = libc_strcpy(src)
expect(dst.len()).to_equal(5)
expect(dst[0]).to_equal(104)
expect(dst[4]).to_equal(111)
```

</details>

#### copies an empty string

- copies an empty string
   - Expected: dst.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("copies an empty string")
val dst = libc_strcpy("".bytes())
expect(dst.len()).to_equal(0)
```

</details>

### strncpy

#### copies when n is larger than source length

- copies when n is larger than source length
   - Expected: dst.len() equals `5`
   - Expected: dst[0] equals `104`
   - Expected: dst[1] equals `105`
   - Expected: dst[2] equals `0`
   - Expected: dst[4] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("copies when n is larger than source length")
val src = "hi".bytes()
val dst = libc_strncpy(src, 5)
expect(dst.len()).to_equal(5)
expect(dst[0]).to_equal(104)
expect(dst[1]).to_equal(105)
expect(dst[2]).to_equal(0)
expect(dst[4]).to_equal(0)
```

</details>

#### truncates when n is smaller than source length

- truncates when n is smaller than source length
   - Expected: dst.len() equals `3`
   - Expected: dst[0] equals `104`
   - Expected: dst[2] equals `108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("truncates when n is smaller than source length")
val src = "hello".bytes()
val dst = libc_strncpy(src, 3)
expect(dst.len()).to_equal(3)
expect(dst[0]).to_equal(104)
expect(dst[2]).to_equal(108)
```

</details>

#### returns empty array when n is 0

- returns empty array when n is 0
   - Expected: dst.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns empty array when n is 0")
val dst = libc_strncpy("hello".bytes(), 0)
expect(dst.len()).to_equal(0)
```

</details>

#### clamps negative n to 0

- clamps negative n to 0
   - Expected: dst.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps negative n to 0")
val dst = libc_strncpy("hello".bytes(), -5)
expect(dst.len()).to_equal(0)
```

</details>

### strcat

#### concatenates two non-empty strings

- concatenates two non-empty strings
   - Expected: result.len() equals `10`
   - Expected: result[0] equals `104`
   - Expected: result[5] equals `119`
   - Expected: result[9] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("concatenates two non-empty strings")
val a = "hello".bytes()
val b = "world".bytes()
val result = libc_strcat(a, b)
expect(result.len()).to_equal(10)
expect(result[0]).to_equal(104)
expect(result[5]).to_equal(119)
expect(result[9]).to_equal(100)
```

</details>

#### concatenates when first is empty

- concatenates when first is empty
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("concatenates when first is empty")
val a = "".bytes()
val b = "hi".bytes()
val result = libc_strcat(a, b)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(104)
```

</details>

#### concatenates when second is empty

- concatenates when second is empty
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("concatenates when second is empty")
val a = "hi".bytes()
val b = "".bytes()
val result = libc_strcat(a, b)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(104)
```

</details>

### strncat

#### concatenates when n is larger than b length

- concatenates when n is larger than b length
   - Expected: result.len() equals `4`
   - Expected: result[0] equals `97`
   - Expected: result[3] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("concatenates when n is larger than b length")
val a = "ab".bytes()
val b = "cd".bytes()
val result = libc_strncat(a, b, 10)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(97)
expect(result[3]).to_equal(100)
```

</details>

#### truncates b when n is smaller than b length

- truncates b when n is smaller than b length
   - Expected: result.len() equals `4`
   - Expected: result[0] equals `97`
   - Expected: result[3] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("truncates b when n is smaller than b length")
val a = "ab".bytes()
val b = "cdef".bytes()
val result = libc_strncat(a, b, 2)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(97)
expect(result[3]).to_equal(100)
```

</details>

#### returns a when n is 0

- returns a when n is 0
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns a when n is 0")
val a = "ab".bytes()
val b = "cd".bytes()
val result = libc_strncat(a, b, 0)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(97)
```

</details>

#### clamps negative n to 0

- clamps negative n to 0
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps negative n to 0")
val a = "ab".bytes()
val b = "cd".bytes()
val result = libc_strncat(a, b, -5)
expect(result.len()).to_equal(2)
```

</details>

### strdup

#### duplicates a non-empty string

- duplicates a non-empty string
   - Expected: dup.len() equals `4`
   - Expected: dup[0] equals `116`
   - Expected: dup[3] equals `116`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("duplicates a non-empty string")
val src = "test".bytes()
val dup = libc_strdup(src)
expect(dup.len()).to_equal(4)
expect(dup[0]).to_equal(116)
expect(dup[3]).to_equal(116)
```

</details>

#### duplicates an empty string

- duplicates an empty string
   - Expected: dup.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("duplicates an empty string")
val dup = libc_strdup("".bytes())
expect(dup.len()).to_equal(0)
```

</details>

### strndup

#### duplicates when n is larger than source length

- duplicates when n is larger than source length
   - Expected: dup.len() equals `2`
   - Expected: dup[0] equals `104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("duplicates when n is larger than source length")
val src = "hi".bytes()
val dup = libc_strndup(src, 10)
expect(dup.len()).to_equal(2)
expect(dup[0]).to_equal(104)
```

</details>

#### truncates when n is smaller than source length

- truncates when n is smaller than source length
   - Expected: dup.len() equals `3`
   - Expected: dup[0] equals `104`
   - Expected: dup[2] equals `108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("truncates when n is smaller than source length")
val src = "hello".bytes()
val dup = libc_strndup(src, 3)
expect(dup.len()).to_equal(3)
expect(dup[0]).to_equal(104)
expect(dup[2]).to_equal(108)
```

</details>

#### returns empty array when n is 0

- returns empty array when n is 0
   - Expected: dup.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns empty array when n is 0")
val dup = libc_strndup("hello".bytes(), 0)
expect(dup.len()).to_equal(0)
```

</details>

#### clamps negative n to 0

- clamps negative n to 0
   - Expected: dup.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps negative n to 0")
val dup = libc_strndup("hello".bytes(), -5)
expect(dup.len()).to_equal(0)
```

</details>

### strnlen

#### returns full length when maxlen is larger

- returns full length when maxlen is larger
   - Expected: libc_strnlen(s, 10) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns full length when maxlen is larger")
val s = "hello".bytes()
expect(libc_strnlen(s, 10)).to_equal(5)
```

</details>

#### returns maxlen when smaller than length

- returns maxlen when smaller than length
   - Expected: libc_strnlen(s, 3) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns maxlen when smaller than length")
val s = "hello".bytes()
expect(libc_strnlen(s, 3)).to_equal(3)
```

</details>

#### returns 0 for empty string

- returns 0 for empty string
   - Expected: libc_strnlen("".bytes(), 10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 0 for empty string")
expect(libc_strnlen("".bytes(), 10)).to_equal(0)
```

</details>

#### clamps negative maxlen to 0

- clamps negative maxlen to 0
   - Expected: libc_strnlen(s, -5) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps negative maxlen to 0")
val s = "hello".bytes()
expect(libc_strnlen(s, -5)).to_equal(0)
```

</details>

### strlcpy

#### copies fully when buffer is large enough

- copies fully when buffer is large enough
   - Expected: r.bytes.len() equals `5`
   - Expected: r.bytes[0] equals `104`
   - Expected: r.total equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("copies fully when buffer is large enough")
val r = libc_strlcpy("hello".bytes(), 10)
expect(r.bytes.len()).to_equal(5)
expect(r.bytes[0]).to_equal(104)
expect(r.total).to_equal(5)
```

</details>

#### truncates to dstsize-1 and reports full source length

- truncates to dstsize-1 and reports full source length
   - Expected: r.bytes.len() equals `2`
   - Expected: r.bytes[0] equals `104`
   - Expected: r.bytes[1] equals `101`
   - Expected: r.total equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("truncates to dstsize-1 and reports full source length")
val r = libc_strlcpy("hello".bytes(), 3)
expect(r.bytes.len()).to_equal(2)
expect(r.bytes[0]).to_equal(104)
expect(r.bytes[1]).to_equal(101)
expect(r.total).to_equal(5)
```

</details>

#### copies nothing for dstsize 0 but still reports source length

- copies nothing for dstsize 0 but still reports source length
   - Expected: r.bytes.len() equals `0`
   - Expected: r.total equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("copies nothing for dstsize 0 but still reports source length")
val r = libc_strlcpy("hi".bytes(), 0)
expect(r.bytes.len()).to_equal(0)
expect(r.total).to_equal(2)
```

</details>

#### copies nothing for dstsize 1 (NUL slot only)

- copies nothing for dstsize 1 (NUL slot only)
   - Expected: r.bytes.len() equals `0`
   - Expected: r.total equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("copies nothing for dstsize 1 (NUL slot only)")
val r = libc_strlcpy("hi".bytes(), 1)
expect(r.bytes.len()).to_equal(0)
expect(r.total).to_equal(2)
```

</details>

### strlcat

<details>
<summary>Advanced: appends when room remains</summary>

#### appends when room remains

- appends when room remains
   - Expected: r.bytes.len() equals `4`
   - Expected: r.bytes[2] equals `99`
   - Expected: r.bytes[3] equals `100`
   - Expected: r.total equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("appends when room remains")
val r = libc_strlcat("ab".bytes(), "cd".bytes(), 10)
expect(r.bytes.len()).to_equal(4)
expect(r.bytes[2]).to_equal(99)
expect(r.bytes[3]).to_equal(100)
expect(r.total).to_equal(4)
```

</details>


</details>

#### truncates appended src to remaining space

- truncates appended src to remaining space
   - Expected: r.bytes.len() equals `4`
   - Expected: r.bytes[3] equals `100`
   - Expected: r.total equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("truncates appended src to remaining space")
val r = libc_strlcat("abc".bytes(), "defg".bytes(), 5)
expect(r.bytes.len()).to_equal(4)
expect(r.bytes[3]).to_equal(100)
expect(r.total).to_equal(7)
```

</details>

#### leaves dst unchanged when buffer already full

- leaves dst unchanged when buffer already full
   - Expected: r.bytes.len() equals `5`
   - Expected: r.total equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("leaves dst unchanged when buffer already full")
val r = libc_strlcat("abcde".bytes(), "x".bytes(), 5)
expect(r.bytes.len()).to_equal(5)
expect(r.total).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_string_copy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS libc — string copy/concat functions, strcpy, strncpy, strcat, strncat, strdup, strndup, strnlen, strlcpy, strlcat.
- SimpleOS libc — string copy/concat functions
- strcpy
- strncpy
- strcat
- strncat
- strdup
- strndup
- strnlen
- strlcpy
- strlcat

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-simpleos-libc-musl-core`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `19336dba8a374b9a4712597f2baeaed850121ad9eef4f3dd3728d0e1dc2ab194`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19336dba8a374b9a4712597f2baeaed850121ad9eef4f3dd3728d0e1dc2ab194`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19336dba8a374b9a4712597f2baeaed850121ad9eef4f3dd3728d0e1dc2ab194`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/libc/libc_string_copy_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_string_copy_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/libc/libc_string_copy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_string_copy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/libc/libc_string_copy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 66 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/libc/libc_string_copy_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/libc/libc_string_copy_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies a non-empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/libc/libc_string_copy_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies an empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/libc/libc_string_copy_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies when n is larger than source length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
