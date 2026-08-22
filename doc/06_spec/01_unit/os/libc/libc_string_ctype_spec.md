# libc_string_ctype_spec

> Verifies the libc string ctype behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# libc_string_ctype_spec

Verifies the libc string ctype behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_string_ctype_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the libc string ctype behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS libc — musl-shaped pure-Simple core

### strlen

#### counts bytes up to NUL or end

- Verify: counts bytes up to NUL or end
   - Expected: libc_strlen("hello".bytes()) equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: libc_strlen("".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: libc_strlen([104, 105, 0, 120]) equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: counts bytes up to NUL or end")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strlen("hello".bytes())).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_strlen("".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_strlen([104, 105, 0, 120])).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strcmp / strncmp

#### returns 0 for equal strings

- Verify: returns 0 for equal strings
   - Expected: libc_strcmp("abc".bytes(), "abc".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: returns 0 for equal strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcmp("abc".bytes(), "abc".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### sign follows first differing byte

- Verify: sign follows first differing byte
   - Expected: libc_strcmp("abc".bytes(), "abd".bytes()) < 0 is true
   - Expected: libc_strcmp("abd".bytes(), "abc".bytes()) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: sign follows first differing byte")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcmp("abc".bytes(), "abd".bytes()) < 0).to_equal(true)
expect(libc_strcmp("abd".bytes(), "abc".bytes()) > 0).to_equal(true)
```

</details>

#### shorter prefix sorts first

- Verify: shorter prefix sorts first
   - Expected: libc_strcmp("ab".bytes(), "abc".bytes()) < 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: shorter prefix sorts first")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcmp("ab".bytes(), "abc".bytes()) < 0).to_equal(true)
```

</details>

#### strncmp stops at n

- Verify: strncmp stops at n
   - Expected: libc_strncmp("abcX".bytes(), "abcY".bytes(), 3) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: libc_strncmp("abcX".bytes(), "abcY".bytes(), 4) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: strncmp stops at n")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strncmp("abcX".bytes(), "abcY".bytes(), 3)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_strncmp("abcX".bytes(), "abcY".bytes(), 4) != 0).to_equal(true)
```

</details>

### strchr / strrchr

#### finds first and last occurrence

- Verify: finds first and last occurrence
   - Expected: libc_strchr("hello".bytes(), 108) equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: libc_strrchr("hello".bytes(), 108) equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: finds first and last occurrence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strchr("hello".bytes(), 108)).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_strrchr("hello".bytes(), 108)).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when absent

- Verify: returns -1 when absent
   - Expected: libc_strchr("hello".bytes(), 122) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: returns -1 when absent")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strchr("hello".bytes(), 122)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### memcmp / memset / memcpy

#### memcmp compares n bytes

- Verify: memcmp compares n bytes
   - Expected: libc_memcmp("abc".bytes(), "abc".bytes(), 3) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: libc_memcmp("abc".bytes(), "abd".bytes(), 3) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: memcmp compares n bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memcmp("abc".bytes(), "abc".bytes(), 3)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_memcmp("abc".bytes(), "abd".bytes(), 3) != 0).to_equal(true)
```

</details>

#### memset fills n bytes

- Verify: memset fills n bytes
   - Expected: m.len() equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m[0] equals `65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: m[3] equals `65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: memset fills n bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m = libc_memset(4, 65)
expect(m.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m[0]).to_equal(65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m[3]).to_equal(65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### memcpy returns first n bytes

- Verify: memcpy returns first n bytes
   - Expected: c.len() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: c[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: c[2] equals `108)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: memcpy returns first n bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val c = libc_memcpy("hello".bytes(), 3)
expect(c.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(c[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(c[2]).to_equal(108)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### atoi / strtol

#### atoi parses decimal with sign and trailing junk

- Verify: atoi parses decimal with sign and trailing junk
   - Expected: libc_atoi("42".bytes()) equals `42)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: libc_atoi("-17".bytes()) equals `-17)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: libc_atoi("  123abc".bytes()) equals `123)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: atoi parses decimal with sign and trailing junk")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_atoi("42".bytes())).to_equal(42)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_atoi("-17".bytes())).to_equal(-17)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_atoi("  123abc".bytes())).to_equal(123)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### strtol parses other bases

- Verify: strtol parses other bases
   - Expected: libc_strtol("ff".bytes(), 16) equals `255)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: libc_strtol("0x1A".bytes(), 16) equals `26)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: libc_strtol("101".bytes(), 2) equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: strtol parses other bases")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strtol("ff".bytes(), 16)).to_equal(255)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_strtol("0x1A".bytes(), 16)).to_equal(26)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_strtol("101".bytes(), 2)).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### ctype

#### classifies ASCII

- Verify: classifies ASCII
   - Expected: libc_isdigit(48) is true
   - Expected: libc_isdigit(58) is false
   - Expected: libc_isalpha(65) is true
   - Expected: libc_isalpha(48) is false
   - Expected: libc_isspace(32) is true
   - Expected: libc_isxdigit(70) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: classifies ASCII")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_isdigit(48)).to_equal(true)
expect(libc_isdigit(58)).to_equal(false)
expect(libc_isalpha(65)).to_equal(true)
expect(libc_isalpha(48)).to_equal(false)
expect(libc_isspace(32)).to_equal(true)
expect(libc_isxdigit(70)).to_equal(true)
```

</details>

#### converts case

- Verify: converts case
   - Expected: libc_toupper(97) equals `65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: libc_tolower(65) equals `97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: libc_toupper(65) equals `65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_CTYPE-001
step("Verify: converts case")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_toupper(97)).to_equal(65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_tolower(65)).to_equal(97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_toupper(65)).to_equal(65)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b1329500928b58a7920f36cfc1294936f5d6fad7885d79b55b95ae622ad1a06`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b1329500928b58a7920f36cfc1294936f5d6fad7885d79b55b95ae622ad1a06`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b1329500928b58a7920f36cfc1294936f5d6fad7885d79b55b95ae622ad1a06`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/libc/libc_string_ctype_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_string_ctype_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/libc/libc_string_ctype_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/libc/libc_string_ctype_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_string_ctype_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
