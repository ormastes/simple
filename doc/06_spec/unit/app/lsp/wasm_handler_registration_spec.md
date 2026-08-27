# Wasm Handler Registration Specification

> Tests covering WASM Handler Registration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Handler Registration Specification

## Scenarios

### WASM Handler Registration

#### Backend selection

#### core parser is WASM mode

- core parser is WASM mode
   - Expected: adapter.is_wasm_mode() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core parser is WASM mode")
val adapter = ParserAdapter.create_core()
expect(adapter.is_wasm_mode()).to_equal(true)
```

</details>

#### treesitter is not WASM mode

- treesitter is not WASM mode
   - Expected: adapter.is_wasm_mode() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treesitter is not WASM mode")
val adapter = ParserAdapter.create_treesitter()
expect(adapter.is_wasm_mode()).to_equal(false)
```

</details>

#### core parser backend enum value

- core parser backend enum value
   - Expected: adapter.backend equals `ParserBackend.CoreParser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core parser backend enum value")
val adapter = ParserAdapter.create_core()
expect(adapter.backend).to_equal(ParserBackend.CoreParser)
```

</details>

#### treesitter backend enum value

- treesitter backend enum value
   - Expected: adapter.backend equals `ParserBackend.TreeSitter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treesitter backend enum value")
val adapter = ParserAdapter.create_treesitter()
expect(adapter.backend).to_equal(ParserBackend.TreeSitter)
```

</details>

#### Parser mode handling

#### core parser handles function definitions

- core parser handles function definitions
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core parser handles function definitions")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("fn hello():\n    print \"hi\"")
expect(result.success).to_equal(true)
```

</details>

#### core parser handles class definitions

- core parser handles class definitions
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core parser handles class definitions")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("class Foo:\n    x: i64")
expect(result.success).to_equal(true)
```

</details>

#### core parser handles struct definitions

- core parser handles struct definitions
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core parser handles struct definitions")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("struct Point:\n    x: i64\n    y: i64")
expect(result.success).to_equal(true)
```

</details>

#### core parser handles import statements

- core parser handles import statements
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core parser handles import statements")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("use std.text.\n")
expect(result.success).to_equal(true)
```

</details>

#### Error detection in WASM mode

#### detects extra closing paren

- detects extra closing paren
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects extra closing paren")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("fn foo(x)): pass")
expect(result.success).to_equal(false)
```

</details>

#### detects extra closing bracket

- detects extra closing bracket
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects extra closing bracket")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val arr = [1, 2]]")
expect(result.success).to_equal(false)
```

</details>

#### does not report errors on valid code

- does not report errors on valid code
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not report errors on valid code")
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = [1, 2, 3]")
expect(result.success).to_equal(true)
```

</details>

#### TreeSitter adapter fallback

#### treesitter parse returns success for any input

- treesitter parse returns success for any input
   - Expected: result.success is true
   - Expected: result.diagnostics.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treesitter parse returns success for any input")
val adapter = ParserAdapter.create_treesitter()
# TreeSitter path returns default success (actual parsing done elsewhere)
val result = adapter.parse("val x = 1")
expect(result.success).to_equal(true)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/wasm_handler_registration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WASM Handler Registration.
- WASM Handler Registration

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61c8c64beebfb449206fa3e518a92f05455db44fdd0ec1e3b443243db7fda12a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61c8c64beebfb449206fa3e518a92f05455db44fdd0ec1e3b443243db7fda12a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61c8c64beebfb449206fa3e518a92f05455db44fdd0ec1e3b443243db7fda12a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/lsp/wasm_handler_registration_spec.spl
mirror: doc/06_spec/unit/app/lsp/wasm_handler_registration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/wasm_handler_registration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/wasm_handler_registration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/wasm_handler_registration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/lsp/wasm_handler_registration_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'core parser is WASM mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/wasm_handler_registration_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treesitter is not WASM mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/wasm_handler_registration_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'core parser backend enum value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
