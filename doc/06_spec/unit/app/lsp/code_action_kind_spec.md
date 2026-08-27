# Code Action Kind Specification

> Tests covering CodeActionKind to_string, CodeActionKind description, CodeActionKind is_quick_fix, CodeActionKind is_refactor, CodeActionKind is_source_action, CodeActionKind is_extract, CodeActionKind is_inline, CodeActionKind summary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Code Action Kind Specification

## Scenarios

### CodeActionKind to_string

#### converts QuickFix to string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts QuickFix to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts QuickFix to string")
# Branch: case QuickFix: "quickfix"
val kind = "quickfix"
expect(kind == "quickfix")
```

</details>

#### converts Refactor to string

- converts Refactor to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Refactor to string")
# Branch: case Refactor: "refactor"
val kind = "refactor"
expect(kind == "refactor")
```

</details>

#### converts RefactorExtract to string

- converts RefactorExtract to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts RefactorExtract to string")
# Branch: case RefactorExtract: "refactor.extract"
val kind = "refactor.extract"
expect(kind == "refactor.extract")
```

</details>

#### converts RefactorInline to string

- converts RefactorInline to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts RefactorInline to string")
# Branch: case RefactorInline: "refactor.inline"
val kind = "refactor.inline"
expect(kind == "refactor.inline")
```

</details>

#### converts RefactorRewrite to string

- converts RefactorRewrite to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts RefactorRewrite to string")
# Branch: case RefactorRewrite: "refactor.rewrite"
val kind = "refactor.rewrite"
expect(kind == "refactor.rewrite")
```

</details>

#### converts Source to string

- converts Source to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Source to string")
# Branch: case Source: "source"
val kind = "source"
expect(kind == "source")
```

</details>

#### converts SourceOrganizeImports to string

- converts SourceOrganizeImports to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts SourceOrganizeImports to string")
# Branch: case SourceOrganizeImports: "source.organizeImports"
val kind = "source.organizeImports"
expect(kind == "source.organizeImports")
```

</details>

### CodeActionKind description

#### describes QuickFix

- describes QuickFix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes QuickFix")
# Branch: case QuickFix: "Quick fix for errors/warnings"
val desc = "Quick fix for errors/warnings"
expect(desc == "Quick fix for errors/warnings")
```

</details>

#### describes Refactor

- describes Refactor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Refactor")
# Branch: case Refactor: "General refactoring"
val desc = "General refactoring"
expect(desc == "General refactoring")
```

</details>

#### describes RefactorExtract

- describes RefactorExtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes RefactorExtract")
# Branch: case RefactorExtract: "Extract code to new element"
val desc = "Extract code to new element"
expect(desc == "Extract code to new element")
```

</details>

#### describes RefactorInline

- describes RefactorInline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes RefactorInline")
# Branch: case RefactorInline: "Inline code"
val desc = "Inline code"
expect(desc == "Inline code")
```

</details>

#### describes RefactorRewrite

- describes RefactorRewrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes RefactorRewrite")
# Branch: case RefactorRewrite: "Rewrite code structure"
val desc = "Rewrite code structure"
expect(desc == "Rewrite code structure")
```

</details>

#### describes Source

- describes Source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Source")
# Branch: case Source: "Source code action"
val desc = "Source code action"
expect(desc == "Source code action")
```

</details>

#### describes SourceOrganizeImports

- describes SourceOrganizeImports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes SourceOrganizeImports")
# Branch: case SourceOrganizeImports: "Organize/sort imports"
val desc = "Organize/sort imports"
expect(desc == "Organize/sort imports")
```

</details>

### CodeActionKind is_quick_fix

#### returns true for QuickFix

- returns true for QuickFix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for QuickFix")
# Branch: case QuickFix: true
val is_fix = true
expect(is_fix)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_fix = false
expect(not is_fix)
```

</details>

### CodeActionKind is_refactor

#### returns true for Refactor

- returns true for Refactor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Refactor")
# Branch: case Refactor: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns true for RefactorExtract

- returns true for RefactorExtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for RefactorExtract")
# Branch: case RefactorExtract: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns true for RefactorInline

- returns true for RefactorInline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for RefactorInline")
# Branch: case RefactorInline: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns true for RefactorRewrite

- returns true for RefactorRewrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for RefactorRewrite")
# Branch: case RefactorRewrite: true
val is_refactor = true
expect(is_refactor)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_refactor = false
expect(not is_refactor)
```

</details>

### CodeActionKind is_source_action

#### returns true for Source

- returns true for Source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Source")
# Branch: case Source: true
val is_source = true
expect(is_source)
```

</details>

#### returns true for SourceOrganizeImports

- returns true for SourceOrganizeImports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for SourceOrganizeImports")
# Branch: case SourceOrganizeImports: true
val is_source = true
expect(is_source)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_source = false
expect(not is_source)
```

</details>

### CodeActionKind is_extract

#### returns true for RefactorExtract

- returns true for RefactorExtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for RefactorExtract")
# Branch: case RefactorExtract: true
val is_extract = true
expect(is_extract)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_extract = false
expect(not is_extract)
```

</details>

### CodeActionKind is_inline

#### returns true for RefactorInline

- returns true for RefactorInline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for RefactorInline")
# Branch: case RefactorInline: true
val is_inline = true
expect(is_inline)
```

</details>

#### returns false for other kinds

- returns false for other kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other kinds")
# Branch: case _: false
val is_inline = false
expect(not is_inline)
```

</details>

### CodeActionKind summary

#### categorizes as fix

- categorizes as fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as fix")
# Branch: if self.is_quick_fix() (true)
val category = "fix"
expect(category == "fix")
```

</details>

#### categorizes as refactor

- categorizes as refactor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as refactor")
# Branch: elif self.is_refactor() (true)
val category = "refactor"
expect(category == "refactor")
```

</details>

#### categorizes as source

- categorizes as source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as source")
# Branch: else (default case)
val category = "source"
expect(category == "source")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/code_action_kind_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CodeActionKind to_string, CodeActionKind description, CodeActionKind is_quick_fix, CodeActionKind is_refactor, CodeActionKind is_source_action, CodeActionKind is_extract, CodeActionKind is_inline, CodeActionKind summary.
- CodeActionKind to_string
- CodeActionKind description
- CodeActionKind is_quick_fix
- CodeActionKind is_refactor
- CodeActionKind is_source_action
- CodeActionKind is_extract
- CodeActionKind is_inline
- CodeActionKind summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `be06c84d05e42b7f43dbe62e1b2a5bd28a1ffa4361984872de9d6f34aadbebd3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be06c84d05e42b7f43dbe62e1b2a5bd28a1ffa4361984872de9d6f34aadbebd3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be06c84d05e42b7f43dbe62e1b2a5bd28a1ffa4361984872de9d6f34aadbebd3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/code_action_kind_spec.spl
mirror: doc/06_spec/unit/app/lsp/code_action_kind_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/code_action_kind_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/code_action_kind_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/code_action_kind_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts QuickFix to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/code_action_kind_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Refactor to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/code_action_kind_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts RefactorExtract to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
