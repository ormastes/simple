# Libc String Ctype Specification

> Tests covering SimpleOS libc — musl-shaped pure-Simple core, strlen, strcmp / strncmp, strchr / strrchr, memcmp / memset / memcpy, atoi / strtol, ctype.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Libc String Ctype Specification

## Scenarios

### SimpleOS libc — musl-shaped pure-Simple core

### strlen

#### counts bytes up to NUL or end

- counts bytes up to NUL or end
   - Expected: libc_strlen("hello".bytes()) equals `5`
   - Expected: libc_strlen("".bytes()) equals `0`
   - Expected: libc_strlen([104, 105, 0, 120]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("counts bytes up to NUL or end")
expect(libc_strlen("hello".bytes())).to_equal(5)
expect(libc_strlen("".bytes())).to_equal(0)
expect(libc_strlen([104, 105, 0, 120])).to_equal(2)
```

</details>

### strcmp / strncmp

#### returns 0 for equal strings

- returns 0 for equal strings
   - Expected: libc_strcmp("abc".bytes(), "abc".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 0 for equal strings")
expect(libc_strcmp("abc".bytes(), "abc".bytes())).to_equal(0)
```

</details>

#### sign follows first differing byte

- sign follows first differing byte
   - Expected: libc_strcmp("abc".bytes(), "abd".bytes()) < 0 is true
   - Expected: libc_strcmp("abd".bytes(), "abc".bytes()) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("sign follows first differing byte")
expect(libc_strcmp("abc".bytes(), "abd".bytes()) < 0).to_equal(true)
expect(libc_strcmp("abd".bytes(), "abc".bytes()) > 0).to_equal(true)
```

</details>

#### shorter prefix sorts first

- shorter prefix sorts first
   - Expected: libc_strcmp("ab".bytes(), "abc".bytes()) < 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("shorter prefix sorts first")
expect(libc_strcmp("ab".bytes(), "abc".bytes()) < 0).to_equal(true)
```

</details>

#### strncmp stops at n

- strncmp stops at n
   - Expected: libc_strncmp("abcX".bytes(), "abcY".bytes(), 3) equals `0`
   - Expected: libc_strncmp("abcX".bytes(), "abcY".bytes(), 4) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("strncmp stops at n")
expect(libc_strncmp("abcX".bytes(), "abcY".bytes(), 3)).to_equal(0)
expect(libc_strncmp("abcX".bytes(), "abcY".bytes(), 4) != 0).to_equal(true)
```

</details>

### strchr / strrchr

#### finds first and last occurrence

- finds first and last occurrence
   - Expected: libc_strchr("hello".bytes(), 108) equals `2`
   - Expected: libc_strrchr("hello".bytes(), 108) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds first and last occurrence")
expect(libc_strchr("hello".bytes(), 108)).to_equal(2)
expect(libc_strrchr("hello".bytes(), 108)).to_equal(3)
```

</details>

#### returns -1 when absent

- returns -1 when absent
   - Expected: libc_strchr("hello".bytes(), 122) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when absent")
expect(libc_strchr("hello".bytes(), 122)).to_equal(-1)
```

</details>

### memcmp / memset / memcpy

#### memcmp compares n bytes

- memcmp compares n bytes
   - Expected: libc_memcmp("abc".bytes(), "abc".bytes(), 3) equals `0`
   - Expected: libc_memcmp("abc".bytes(), "abd".bytes(), 3) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("memcmp compares n bytes")
expect(libc_memcmp("abc".bytes(), "abc".bytes(), 3)).to_equal(0)
expect(libc_memcmp("abc".bytes(), "abd".bytes(), 3) != 0).to_equal(true)
```

</details>

#### memset fills n bytes

- memset fills n bytes
   - Expected: m.len() equals `4`
   - Expected: m[0] equals `65`
   - Expected: m[3] equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("memset fills n bytes")
val m = libc_memset(4, 65)
expect(m.len()).to_equal(4)
expect(m[0]).to_equal(65)
expect(m[3]).to_equal(65)
```

</details>

#### memcpy returns first n bytes

- memcpy returns first n bytes
   - Expected: c.len() equals `3`
   - Expected: c[0] equals `104`
   - Expected: c[2] equals `108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("memcpy returns first n bytes")
val c = libc_memcpy("hello".bytes(), 3)
expect(c.len()).to_equal(3)
expect(c[0]).to_equal(104)
expect(c[2]).to_equal(108)
```

</details>

### atoi / strtol

#### atoi parses decimal with sign and trailing junk

- atoi parses decimal with sign and trailing junk
   - Expected: libc_atoi("42".bytes()) equals `42`
   - Expected: libc_atoi("-17".bytes()) equals `-17`
   - Expected: libc_atoi("  123abc".bytes()) equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("atoi parses decimal with sign and trailing junk")
expect(libc_atoi("42".bytes())).to_equal(42)
expect(libc_atoi("-17".bytes())).to_equal(-17)
expect(libc_atoi("  123abc".bytes())).to_equal(123)
```

</details>

#### strtol parses other bases

- strtol parses other bases
   - Expected: libc_strtol("ff".bytes(), 16) equals `255`
   - Expected: libc_strtol("0x1A".bytes(), 16) equals `26`
   - Expected: libc_strtol("101".bytes(), 2) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("strtol parses other bases")
expect(libc_strtol("ff".bytes(), 16)).to_equal(255)
expect(libc_strtol("0x1A".bytes(), 16)).to_equal(26)
expect(libc_strtol("101".bytes(), 2)).to_equal(5)
```

</details>

### ctype

#### classifies ASCII

- classifies ASCII
   - Expected: libc_isdigit(48) is true
   - Expected: libc_isdigit(58) is false
   - Expected: libc_isalpha(65) is true
   - Expected: libc_isalpha(48) is false
   - Expected: libc_isspace(32) is true
   - Expected: libc_isxdigit(70) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("classifies ASCII")
expect(libc_isdigit(48)).to_equal(true)
expect(libc_isdigit(58)).to_equal(false)
expect(libc_isalpha(65)).to_equal(true)
expect(libc_isalpha(48)).to_equal(false)
expect(libc_isspace(32)).to_equal(true)
expect(libc_isxdigit(70)).to_equal(true)
```

</details>

#### converts case

- converts case
   - Expected: libc_toupper(97) equals `65`
   - Expected: libc_tolower(65) equals `97`
   - Expected: libc_toupper(65) equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("converts case")
expect(libc_toupper(97)).to_equal(65)
expect(libc_tolower(65)).to_equal(97)
expect(libc_toupper(65)).to_equal(65)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_string_ctype_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS libc — musl-shaped pure-Simple core, strlen, strcmp / strncmp, strchr / strrchr, memcmp / memset / memcpy, atoi / strtol, ctype.
- SimpleOS libc — musl-shaped pure-Simple core
- strlen
- strcmp / strncmp
- strchr / strrchr
- memcmp / memset / memcpy
- atoi / strtol
- ctype

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `a2917dc5f7566155a860cb583068e75c5f0e926e1b0cfe4df3e842f527017eba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2917dc5f7566155a860cb583068e75c5f0e926e1b0cfe4df3e842f527017eba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2917dc5f7566155a860cb583068e75c5f0e926e1b0cfe4df3e842f527017eba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/libc/libc_string_ctype_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_string_ctype_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/libc/libc_string_ctype_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_string_ctype_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/libc/libc_string_ctype_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/libc/libc_string_ctype_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/libc/libc_string_ctype_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts bytes up to NUL or end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/libc/libc_string_ctype_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for equal strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/libc/libc_string_ctype_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sign follows first differing byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
