# Tier Keywords Specification

> Tests covering tier_keywords.sdn, tier_keywords.sdn content validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tier Keywords Specification

## Scenarios

### tier_keywords.sdn

#### exists at expected path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exists at expected path
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exists at expected path")
val found = rt_file_exists("doc/06_spec/grammar/tier_keywords.sdn")
expect(found).to_equal(true)
```

</details>

#### is non-empty

- is non-empty
   - Expected: text_content.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is non-empty")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.len() > 0).to_equal(true)
```

</details>

#### contains keywords.declarations section

- contains keywords.declarations section
   - Expected: text_content contains `[keywords.declarations]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains keywords.declarations section")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[keywords.declarations]")).to_equal(true)
```

</details>

#### contains keywords.control_flow section

- contains keywords.control_flow section
   - Expected: text_content contains `[keywords.control_flow]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains keywords.control_flow section")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[keywords.control_flow]")).to_equal(true)
```

</details>

#### contains keywords.expressions section

- contains keywords.expressions section
   - Expected: text_content contains `[keywords.expressions]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains keywords.expressions section")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[keywords.expressions]")).to_equal(true)
```

</details>

#### contains operators section

- contains operators section
   - Expected: text_content contains `[operators]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains operators section")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[operators]")).to_equal(true)
```

</details>

#### contains constructs section

- contains constructs section
   - Expected: text_content contains `[constructs]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains constructs section")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[constructs]")).to_equal(true)
```

</details>

#### classifies fn as seed

- classifies fn as seed
   - Expected: text_content contains `fn = "seed"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies fn as seed")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("fn = \"seed\"")).to_equal(true)
```

</details>

#### classifies trait as core

- classifies trait as core
   - Expected: text_content contains `trait = "core"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies trait as core")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("trait = \"core\"")).to_equal(true)
```

</details>

#### classifies actor as full

- classifies actor as full
   - Expected: text_content contains `actor = "full"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies actor as full")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("actor = \"full\"")).to_equal(true)
```

</details>

#### classifies try as full

- classifies try as full
   - Expected: text_content contains `try = "full"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies try as full")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("try = \"full\"")).to_equal(true)
```

</details>

#### has treesitter_aspirational section

- has treesitter_aspirational section
   - Expected: text_content contains `[treesitter_aspirational]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has treesitter_aspirational section")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[treesitter_aspirational]")).to_equal(true)
```

</details>

### tier_keywords.sdn content validation

#### all seed keywords are present

- all seed keywords are present
   - Expected: text_content contains `val = "seed"`
   - Expected: text_content contains `var = "seed"`
   - Expected: text_content contains `struct = "seed"`
   - Expected: text_content contains `if = "seed"`
   - Expected: text_content contains `for = "seed"`
   - Expected: text_content contains `return = "seed"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all seed keywords are present")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
# Check core seed keywords exist
expect(text_content.contains("val = \"seed\"")).to_equal(true)
expect(text_content.contains("var = \"seed\"")).to_equal(true)
expect(text_content.contains("struct = \"seed\"")).to_equal(true)
expect(text_content.contains("if = \"seed\"")).to_equal(true)
expect(text_content.contains("for = \"seed\"")).to_equal(true)
expect(text_content.contains("return = \"seed\"")).to_equal(true)
```

</details>

#### all core keywords are present

- all core keywords are present
   - Expected: text_content contains `loop = "core"`
   - Expected: text_content contains `pass = "core"`
   - Expected: text_content contains `self = "core"`
   - Expected: text_content contains `async = "core"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all core keywords are present")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("loop = \"core\"")).to_equal(true)
expect(text_content.contains("pass = \"core\"")).to_equal(true)
expect(text_content.contains("self = \"core\"")).to_equal(true)
expect(text_content.contains("async = \"core\"")).to_equal(true)
```

</details>

#### contains all three tier values

- contains all three tier values
   - Expected: text_content contains `= "seed"`
   - Expected: text_content contains `= "core"`
   - Expected: text_content contains `= "full"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains all three tier values")
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
# Verify that all three tier values appear in the file
expect(text_content.contains("= \"seed\"")).to_equal(true)
expect(text_content.contains("= \"core\"")).to_equal(true)
expect(text_content.contains("= \"full\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/grammar_doc/tier_keywords_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tier_keywords.sdn, tier_keywords.sdn content validation.
- tier_keywords.sdn
- tier_keywords.sdn content validation

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e64905b901905f00ab044bb9b0c08d3d30243549c6df14906c0ccfc7e0ae768`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e64905b901905f00ab044bb9b0c08d3d30243549c6df14906c0ccfc7e0ae768`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e64905b901905f00ab044bb9b0c08d3d30243549c6df14906c0ccfc7e0ae768`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/grammar_doc/tier_keywords_spec.spl
mirror: doc/06_spec/unit/app/grammar_doc/tier_keywords_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/grammar_doc/tier_keywords_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/grammar_doc/tier_keywords_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/grammar_doc/tier_keywords_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exists at expected path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/grammar_doc/tier_keywords_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/grammar_doc/tier_keywords_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains keywords.declarations section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
