# Unicode Codepoint Specification

> Tests covering std.common.unicode.codepoint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unicode Codepoint Specification

## Scenarios

### std.common.unicode.codepoint

#### maps ASCII case in both directions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps ASCII case in both directions
   - Expected: unicode_to_upper(0x61) equals `0x41)      # a -> A`
   - Expected: unicode_to_lower(0x5A) equals `0x7A)      # Z -> z`
   - Expected: unicode_to_upper(0x41) equals `0x41)      # A unchanged`
   - Expected: unicode_to_lower(0x7A) equals `0x7A)      # z unchanged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps ASCII case in both directions")
expect(unicode_to_upper(0x61)).to_equal(0x41)      # a -> A
expect(unicode_to_lower(0x5A)).to_equal(0x7A)      # Z -> z
expect(unicode_to_upper(0x41)).to_equal(0x41)      # A unchanged
expect(unicode_to_lower(0x7A)).to_equal(0x7A)      # z unchanged
```

</details>

#### maps Latin-1 case and skips the two maths signs

- maps Latin-1 case and skips the two maths signs
   - Expected: unicode_to_upper(0xE0) equals `0xC0)      # a-grave -> A-grave`
   - Expected: unicode_to_lower(0xD6) equals `0xF6)      # O-diaeresis`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps Latin-1 case and skips the two maths signs")
expect(unicode_to_upper(0xE0)).to_equal(0xC0)      # a-grave -> A-grave
expect(unicode_to_lower(0xD6)).to_equal(0xF6)      # O-diaeresis
# U+00D7 multiplication and U+00F7 division are not letters.
assert_false(is_unicode_upper(0xD7))
assert_false(is_unicode_lower(0xF7))
assert_false(is_unicode_letter(0xD7))
```

</details>

#### leaves characters with no simple uppercase alone

- leaves characters with no simple uppercase alone
   - Expected: unicode_to_upper(0xDF) equals `0xDF`
   - Expected: unicode_to_upper(0x138) equals `0x138)    # kra`
   - Expected: unicode_to_upper(0x149) equals `0x149`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves characters with no simple uppercase alone")
# Sharp s uppercases to "SS", which simple case mapping cannot
# express, so it must be returned unchanged rather than mangled.
expect(unicode_to_upper(0xDF)).to_equal(0xDF)
expect(unicode_to_upper(0x138)).to_equal(0x138)    # kra
expect(unicode_to_upper(0x149)).to_equal(0x149)
```

</details>

#### handles the Latin Extended-A parity flips

- handles the Latin Extended-A parity flips
   - Expected: unicode_to_upper(0x101) equals `0x100`
   - Expected: unicode_to_lower(0x100) equals `0x101`
   - Expected: unicode_to_upper(0x13A) equals `0x139`
   - Expected: unicode_to_lower(0x139) equals `0x13A`
   - Expected: unicode_to_upper(0x17A) equals `0x179`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles the Latin Extended-A parity flips")
# 0x100..0x137 even = upper
expect(unicode_to_upper(0x101)).to_equal(0x100)
expect(unicode_to_lower(0x100)).to_equal(0x101)
# 0x139..0x148 odd = upper -- a naive even/odd test gets this wrong
assert_true(is_unicode_upper(0x139))
assert_true(is_unicode_lower(0x13A))
expect(unicode_to_upper(0x13A)).to_equal(0x139)
expect(unicode_to_lower(0x139)).to_equal(0x13A)
# 0x14A..0x177 back to even = upper
assert_true(is_unicode_upper(0x14A))
# 0x179..0x17E odd = upper again
assert_true(is_unicode_upper(0x179))
expect(unicode_to_upper(0x17A)).to_equal(0x179)
```

</details>

#### handles the Latin special-case round trips

- handles the Latin special-case round trips
   - Expected: unicode_to_upper(0xFF) equals `0x178)     # y-diaeresis`
   - Expected: unicode_to_lower(0x178) equals `0xFF`
   - Expected: unicode_to_upper(0x131) equals `0x49)     # dotless i -> I`
   - Expected: unicode_to_lower(0x130) equals `0x69)     # I-with-dot -> i`
   - Expected: unicode_to_upper(0x17F) equals `0x53)     # long s -> S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles the Latin special-case round trips")
expect(unicode_to_upper(0xFF)).to_equal(0x178)     # y-diaeresis
expect(unicode_to_lower(0x178)).to_equal(0xFF)
expect(unicode_to_upper(0x131)).to_equal(0x49)     # dotless i -> I
expect(unicode_to_lower(0x130)).to_equal(0x69)     # I-with-dot -> i
expect(unicode_to_upper(0x17F)).to_equal(0x53)     # long s -> S
```

</details>

#### maps Greek case including final sigma

- maps Greek case including final sigma
   - Expected: unicode_to_upper(0x3B1) equals `0x391)    # alpha`
   - Expected: unicode_to_lower(0x391) equals `0x3B1`
   - Expected: unicode_to_upper(0x3C9) equals `0x3A9)    # omega`
   - Expected: unicode_to_upper(0x3C2) equals `0x3A3`
   - Expected: unicode_to_upper(0x3C3) equals `0x3A3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps Greek case including final sigma")
expect(unicode_to_upper(0x3B1)).to_equal(0x391)    # alpha
expect(unicode_to_lower(0x391)).to_equal(0x3B1)
expect(unicode_to_upper(0x3C9)).to_equal(0x3A9)    # omega
# Final sigma and medial sigma both uppercase to capital sigma.
expect(unicode_to_upper(0x3C2)).to_equal(0x3A3)
expect(unicode_to_upper(0x3C3)).to_equal(0x3A3)
```

</details>

#### maps Cyrillic case in both sub-ranges

- maps Cyrillic case in both sub-ranges
   - Expected: unicode_to_upper(0x430) equals `0x410)    # a`
   - Expected: unicode_to_lower(0x410) equals `0x430`
   - Expected: unicode_to_upper(0x451) equals `0x401)    # yo`
   - Expected: unicode_to_lower(0x401) equals `0x451`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps Cyrillic case in both sub-ranges")
expect(unicode_to_upper(0x430)).to_equal(0x410)    # a
expect(unicode_to_lower(0x410)).to_equal(0x430)
expect(unicode_to_upper(0x451)).to_equal(0x401)    # yo
expect(unicode_to_lower(0x401)).to_equal(0x451)
```

</details>

#### classifies letters across cased and caseless scripts

- classifies letters across cased and caseless scripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies letters across cased and caseless scripts")
assert_true(is_unicode_letter(0x41))     # A
assert_true(is_unicode_letter(0x3B1))    # alpha
assert_true(is_unicode_letter(0x5D0))    # Hebrew alef
assert_true(is_unicode_letter(0x4E00))   # CJK
assert_true(is_unicode_letter(0xAC00))   # Hangul
assert_true(is_unicode_letter(0x30A2))   # Katakana
assert_false(is_unicode_letter(0x30))    # digit 0
assert_false(is_unicode_letter(0x20))    # space
```

</details>

#### classifies decimal digits beyond ASCII

- classifies decimal digits beyond ASCII


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies decimal digits beyond ASCII")
assert_true(is_unicode_digit(0x39))      # 9
assert_true(is_unicode_digit(0x660))     # Arabic-Indic 0
assert_true(is_unicode_digit(0x966))     # Devanagari 0
assert_true(is_unicode_digit(0xFF19))    # fullwidth 9
assert_false(is_unicode_digit(0x41))     # A
# U+2160 ROMAN NUMERAL ONE is Nl, not Nd.
assert_false(is_unicode_digit(0x2160))
```

</details>

#### classifies Unicode whitespace

- classifies Unicode whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies Unicode whitespace")
assert_true(is_unicode_whitespace(0x20))
assert_true(is_unicode_whitespace(0x09))
assert_true(is_unicode_whitespace(0xA0)) # no-break space
assert_true(is_unicode_whitespace(0x2003))  # em space
assert_true(is_unicode_whitespace(0x3000))  # ideographic
assert_false(is_unicode_whitespace(0x41))
# U+200B ZERO WIDTH SPACE is NOT White_Space.
assert_false(is_unicode_whitespace(0x200B))
```

</details>

#### classifies combining marks

- classifies combining marks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies combining marks")
assert_true(is_combining_mark(0x301))    # acute
assert_true(is_combining_mark(0x64B))    # Arabic fathatan
assert_true(is_combining_mark(0x20E3))   # enclosing keycap
assert_false(is_combining_mark(0x41))
assert_false(is_combining_mark(0x20))
```

</details>

#### round-trips case for every ASCII letter

- round-trips case for every ASCII letter
   - Expected: mismatches equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips case for every ASCII letter")
var i: i64 = 0x41
var mismatches: i64 = 0
while i <= 0x5A:
    if unicode_to_upper(unicode_to_lower(i)) != i:
        mismatches = mismatches + 1
    i = i + 1
expect(mismatches).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/unicode_codepoint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.common.unicode.codepoint.
- std.common.unicode.codepoint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ffe6ebc665fe3ae100acc3e832352d46f3dc363d2d8d7fa7495675f87b7cdbf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ffe6ebc665fe3ae100acc3e832352d46f3dc363d2d8d7fa7495675f87b7cdbf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ffe6ebc665fe3ae100acc3e832352d46f3dc363d2d8d7fa7495675f87b7cdbf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/unicode_codepoint_spec.spl
mirror: doc/06_spec/01_unit/lib/unicode_codepoint_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/unicode_codepoint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/unicode_codepoint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/unicode_codepoint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/unicode_codepoint_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps ASCII case in both directions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/unicode_codepoint_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps Latin-1 case and skips the two maths signs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/unicode_codepoint_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves characters with no simple uppercase alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
