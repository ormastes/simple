# String Helpers Hex Specification

> Tests covering app.io.string_helpers, hex_to_char, byte_to_char, char_code, text_hash_native.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Helpers Hex Specification

## Scenarios

### app.io.string_helpers

### hex_to_char

#### converts ASCII codes

- converts ASCII codes
   - Expected: hex_to_char(65) equals `A`
   - Expected: hex_to_char(97) equals `a`
   - Expected: hex_to_char(48) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("converts ASCII codes")
expect(hex_to_char(65)).to_equal("A")
expect(hex_to_char(97)).to_equal("a")
expect(hex_to_char(48)).to_equal("0")
```

</details>

#### converts zero

- converts zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("converts zero")
val result = hex_to_char(0)
expect(result.len()).to_be_greater_than(0)
```

</details>

### byte_to_char

#### is alias for hex_to_char

- is alias for hex_to_char
   - Expected: byte_to_char(65) equals `A`
   - Expected: byte_to_char(90) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is alias for hex_to_char")
expect(byte_to_char(65)).to_equal("A")
expect(byte_to_char(90)).to_equal("Z")
```

</details>

### char_code

#### returns 0 for empty string

- returns 0 for empty string
   - Expected: char_code("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns 0 for empty string")
expect(char_code("")).to_equal(0)
```

</details>

### text_hash_native

#### returns consistent hash

- returns consistent hash
   - Expected: h1 equals `h2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns consistent hash")
val h1 = text_hash_native("hello")
val h2 = text_hash_native("hello")
expect(h1).to_equal(h2)
```

</details>

#### returns different hashes for different lengths

- returns different hashes for different lengths
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns different hashes for different lengths")
val h1 = text_hash_native("a")
val h2 = text_hash_native("ab")
val same = h1 == h2
expect(same).to_equal(false)
```

</details>

#### handles empty string

- handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles empty string")
val h = text_hash_native("")
expect(h).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/string_helpers_hex_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app.io.string_helpers, hex_to_char, byte_to_char, char_code, text_hash_native.
- app.io.string_helpers
- hex_to_char
- byte_to_char
- char_code
- text_hash_native

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5636970c440d945ff24f9d7481a907a2b4187de85a49a3a63082c3e95f181784`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5636970c440d945ff24f9d7481a907a2b4187de85a49a3a63082c3e95f181784`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5636970c440d945ff24f9d7481a907a2b4187de85a49a3a63082c3e95f181784`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/io/string_helpers_hex_spec.spl
mirror: doc/06_spec/01_unit/app/io/string_helpers_hex_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/string_helpers_hex_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/string_helpers_hex_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/string_helpers_hex_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/io/string_helpers_hex_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts ASCII codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/string_helpers_hex_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/string_helpers_hex_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is alias for hex_to_char' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
