# Wasm Document Management Specification

> Tests covering WASM Document Management.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Document Management Specification

## Scenarios

### WASM Document Management

#### Parsing Simple documents

#### parses simple variable declaration

- parses simple variable declaration
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple variable declaration")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val name = \"Alice\"")
expect(result.success).to_equal(true)
```

</details>

#### parses mutable variable

- parses mutable variable
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mutable variable")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("var count = 0")
expect(result.success).to_equal(true)
```

</details>

#### parses function with body

- parses function with body
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses function with body")
val adapter = ParserAdapter.create_core()
val code = "fn square(x: i64) -> i64:\n    x * x"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### parses empty string

- parses empty string
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty string")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("")
expect(result.success).to_equal(true)
```

</details>

#### parses whitespace only

- parses whitespace only
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses whitespace only")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("   \n   \n")
expect(result.success).to_equal(true)
```

</details>

#### Bracket error detection

#### reports error line for unmatched paren

- reports error line for unmatched paren
   - Expected: result.diagnostics[0].line equals `0`
   - Expected: result.diagnostics[0].severity equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports error line for unmatched paren")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = )")
expect(result.diagnostics.len()).to_be_greater_than(0)
expect(result.diagnostics[0].line).to_equal(0)
expect(result.diagnostics[0].severity).to_equal(1)
```

</details>

#### reports error for unmatched bracket

- reports error for unmatched bracket
   - Expected: result.diagnostics[0].line equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports error for unmatched bracket")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val arr = ]")
expect(result.diagnostics.len()).to_be_greater_than(0)
expect(result.diagnostics[0].line).to_equal(0)
```

</details>

#### handles nested brackets correctly

- handles nested brackets correctly
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested brackets correctly")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = [[1, 2], [3, 4]]")
expect(result.success).to_equal(true)
```

</details>

#### handles mixed brackets and parens

- handles mixed brackets and parens
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mixed brackets and parens")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = foo([1, 2], (3 + 4))")
expect(result.success).to_equal(true)
```

</details>

#### Multi-line document parsing

#### parses describe/it test blocks

- parses describe/it test blocks
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses describe/it test blocks")
val adapter = ParserAdapter.create_core()
val code = "describe \"test\":\n    it \"works\":\n        expect(1).to_equal(1)"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### parses class with methods

- parses class with methods
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses class with methods")
val adapter = ParserAdapter.create_core()
val code = "class Counter:\n    count: i64\n    me increment():\n        self.count = self.count + 1"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### parses enum definitions

- parses enum definitions
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses enum definitions")
val adapter = ParserAdapter.create_core()
val code = "enum Color:\n    Red\n    Green\n    Blue"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### Diagnostic properties

#### diagnostic has correct message for paren

- diagnostic has correct message for paren


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diagnostic has correct message for paren")
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")")
expect(result.diagnostics[0].message).to_contain("parenthesis")
```

</details>

#### diagnostic has correct message for bracket

- diagnostic has correct message for bracket


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diagnostic has correct message for bracket")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("]")
expect(result.diagnostics[0].message).to_contain("bracket")
```

</details>

#### diagnostic has error severity

- diagnostic has error severity
   - Expected: result.diagnostics[0].severity equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diagnostic has error severity")
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")")
expect(result.diagnostics[0].severity).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/wasm_document_management_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WASM Document Management.
- WASM Document Management

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

- Canonical SPipe generation for source `bc6320c81a283b4c8c214fd0627e7e782dc3dd218a75487006e3b4c84604129d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc6320c81a283b4c8c214fd0627e7e782dc3dd218a75487006e3b4c84604129d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc6320c81a283b4c8c214fd0627e7e782dc3dd218a75487006e3b4c84604129d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/lsp/wasm_document_management_spec.spl
mirror: doc/06_spec/unit/app/lsp/wasm_document_management_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/wasm_document_management_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/wasm_document_management_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/wasm_document_management_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/lsp/wasm_document_management_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple variable declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/wasm_document_management_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses mutable variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/wasm_document_management_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function with body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
