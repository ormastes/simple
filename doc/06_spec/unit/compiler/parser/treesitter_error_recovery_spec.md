# Treesitter Error Recovery Specification

> Tests covering TreeSitter Error Recovery.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Error Recovery Specification

## Scenarios

### TreeSitter Error Recovery

#### recovers after malformed function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recovers after malformed function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recovers after malformed function")
val src = "fn broken(:\n    1\n\nfn valid():\n    2\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
# Should still find the valid function after error recovery
expect(outline.functions.len()).to_be_greater_than(0)
```

</details>

#### parses valid code after syntax error

- parses valid code after syntax error
   - Expected: outline.functions.len() equals `1`
   - Expected: outline.functions[0].name equals `good`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses valid code after syntax error")
val src = "class :\n\nfn good():\n    42\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.functions.len()).to_equal(1)
expect(outline.functions[0].name).to_equal("good")
```

</details>

#### collects errors from malformed source

- collects errors from malformed source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects errors from malformed source")
val src = "fn ():\n    pass\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.errors.len()).to_be_greater_than(0)
```

</details>

#### produces empty outline for gibberish

- produces empty outline for gibberish


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces empty outline for gibberish")
var ts = TreeSitter.new("!@#$%^&*")
val outline = ts.parse_outline()
expect(outline.errors.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/treesitter_error_recovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TreeSitter Error Recovery.
- TreeSitter Error Recovery

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `f534141ee5052c44f9ca496e9ee7602d58af6c559a5f4b75396f9f8762bc3a11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f534141ee5052c44f9ca496e9ee7602d58af6c559a5f4b75396f9f8762bc3a11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f534141ee5052c44f9ca496e9ee7602d58af6c559a5f4b75396f9f8762bc3a11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/parser/treesitter_error_recovery_spec.spl
mirror: doc/06_spec/unit/compiler/parser/treesitter_error_recovery_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/treesitter_error_recovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/treesitter_error_recovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/treesitter_error_recovery_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/treesitter_error_recovery_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recovers after malformed function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_error_recovery_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses valid code after syntax error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_error_recovery_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects errors from malformed source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
