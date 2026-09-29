# Pattern Binding Specification

> Tests covering pattern binding in match.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Binding Specification

## Scenarios

### pattern binding in match

#### matched value used via original variable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matched value used via original variable
   - Expected: result equals `84`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matched value used via original variable")
val x = 42
val result = match x:
    case 42: x * 2
    case _: 0
expect(result).to_equal(84)
```

</details>

#### match with guard uses enclosing scope

- match with guard uses enclosing scope
   - Expected: result equals `big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match with guard uses enclosing scope")
val x = 10
val result = match x:
    case 10 if x > 5: "big"
    case _: "small"
expect(result).to_equal("big")
```

</details>

#### wildcard works without binding

- wildcard works without binding
   - Expected: result equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wildcard works without binding")
val x = 99
val result = match x:
    case 42: "forty-two"
    case _: "other"
expect(result).to_equal("other")
```

</details>

#### string pattern matched via function

- string pattern matched via function
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string pattern matched via function")
val result = check_word("hello")
expect(result).to_equal("hello world")
```

</details>

#### extract function uses matched literal

- extract function uses matched literal
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract function uses matched literal")
val result = extract_number(10)
expect(result).to_equal(15)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/pattern_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pattern binding in match.
- pattern binding in match

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `2596aa0f8e7dc2996c5dba8fc664747684e5030b9f0de094e7b281e1243635d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2596aa0f8e7dc2996c5dba8fc664747684e5030b9f0de094e7b281e1243635d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2596aa0f8e7dc2996c5dba8fc664747684e5030b9f0de094e7b281e1243635d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/parser/pattern_binding_spec.spl
mirror: doc/06_spec/unit/compiler/parser/pattern_binding_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/pattern_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/pattern_binding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/pattern_binding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/pattern_binding_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matched value used via original variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/pattern_binding_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'match with guard uses enclosing scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/pattern_binding_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wildcard works without binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
