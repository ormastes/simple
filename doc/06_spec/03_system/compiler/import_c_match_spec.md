# Import C Match Specification

> Tests covering import_c match — name normalization, import_c match — strict vs non-strict, import_c match — aka field aliases, import_c match — field coverage validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import C Match Specification

## Scenarios

### import_c match — name normalization

#### normalize_c_name strips underscores and lowercases

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalize_c_name strips underscores and lowercases
   - Expected: src contains `fn normalize_c_name(name: text) -> text`
   - Expected: src contains `ch != "_"`
   - Expected: src contains `ch != "-"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalize_c_name strips underscores and lowercases")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn normalize_c_name(name: text) -> text")).to_equal(true)
expect(src.contains("ch != \"_\"")).to_equal(true)
expect(src.contains("ch != \"-\"")).to_equal(true)
```

</details>

#### lowercases via char_code_at + 32

- lowercases via char_code_at + 32
   - Expected: src contains `ch >= "A" and ch <= "Z"`
   - Expected: src contains `code + 32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lowercases via char_code_at + 32")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("ch >= \"A\" and ch <= \"Z\"")).to_equal(true)
expect(src.contains("code + 32")).to_equal(true)
```

</details>

### import_c match — strict vs non-strict

#### c_names_match uses normalize_c_name for both sides

- c_names_match uses normalize_c_name for both sides
   - Expected: src contains `normalize_c_name(simple_name) == normalize_c_name(c_name)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("c_names_match uses normalize_c_name for both sides")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("normalize_c_name(simple_name) == normalize_c_name(c_name)")).to_equal(true)
```

</details>

#### c_names_match_strict uses exact equality

- c_names_match_strict uses exact equality
   - Expected: src contains `simple_name == c_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("c_names_match_strict uses exact equality")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("simple_name == c_name")).to_equal(true)
```

</details>

#### CImportMatch has strict flag

- CImportMatch has strict flag
   - Expected: src contains `strict: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CImportMatch has strict flag")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("strict: bool")).to_equal(true)
```

</details>

#### CImport has strict_match default

- CImport has strict_match default
   - Expected: src contains `strict_match: bool`
   - Expected: src contains `strict_match: false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CImport has strict_match default")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("strict_match: bool")).to_equal(true)
expect(src.contains("strict_match: false")).to_equal(true)
```

</details>

### import_c match — aka field aliases

#### CImportedField has aka_name field

- CImportedField has aka_name field
   - Expected: src contains `aka_name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CImportedField has aka_name field")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("aka_name: text")).to_equal(true)
```

</details>

#### find_aka_field performs exact match on C field names

- find_aka_field performs exact match on C field names
   - Expected: src contains `fn find_aka_field(aka_name: text, c_field_names: [text]) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("find_aka_field performs exact match on C field names")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn find_aka_field(aka_name: text, c_field_names: [text]) -> text")).to_equal(true)
```

</details>

#### aka takes priority over auto-matching

- aka takes priority over auto-matching
   - Expected: src contains `sf.aka_name != ""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aka takes priority over auto-matching")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("sf.aka_name != \"\"")).to_equal(true)
```

</details>

#### aka referencing nonexistent field produces error

- aka referencing nonexistent field produces error
   - Expected: src contains `aka field not found in C struct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aka referencing nonexistent field produces error")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("aka field not found in C struct")).to_equal(true)
```

</details>

### import_c match — field coverage validation

#### extra Simple field (not in C) produces error

- extra Simple field (not in C) produces error
   - Expected: src contains `field has no match in C struct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extra Simple field (not in C) produces error")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("field has no match in C struct")).to_equal(true)
```

</details>

#### extra C field (not in Simple) tracked as unmatched_c

- extra C field (not in Simple) tracked as unmatched_c
   - Expected: src contains `unmatched_c: [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extra C field (not in Simple) tracked as unmatched_c")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("unmatched_c: [text]")).to_equal(true)
```

</details>

#### validate_field_match collects all errors

- validate_field_match collects all errors
   - Expected: src contains `fn validate_field_match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validate_field_match collects all errors")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn validate_field_match")).to_equal(true)
```

</details>

#### FieldMatch records simple_name, c_name, and aka_name

- FieldMatch records simple_name, c_name, and aka_name
   - Expected: src contains `struct FieldMatch:`
   - Expected: src contains `simple_name: text`
   - Expected: src contains `c_name: text`
   - Expected: src contains `aka_name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FieldMatch records simple_name, c_name, and aka_name")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("struct FieldMatch:")).to_equal(true)
expect(src.contains("simple_name: text")).to_equal(true)
expect(src.contains("c_name: text")).to_equal(true)
expect(src.contains("aka_name: text")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/import_c_match_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering import_c match — name normalization, import_c match — strict vs non-strict, import_c match — aka field aliases, import_c match — field coverage validation.
- import_c match — name normalization
- import_c match — strict vs non-strict
- import_c match — aka field aliases
- import_c match — field coverage validation

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6eee5eaf9dd7132253144999f1793a4fc8f84a82c75ca00aede30f84fcf02acc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6eee5eaf9dd7132253144999f1793a4fc8f84a82c75ca00aede30f84fcf02acc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6eee5eaf9dd7132253144999f1793a4fc8f84a82c75ca00aede30f84fcf02acc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/import_c_match_spec.spl
mirror: doc/06_spec/03_system/compiler/import_c_match_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/import_c_match_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/import_c_match_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/import_c_match_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalize_c_name strips underscores and lowercases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/import_c_match_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowercases via char_code_at + 32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/import_c_match_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'c_names_match uses normalize_c_name for both sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
