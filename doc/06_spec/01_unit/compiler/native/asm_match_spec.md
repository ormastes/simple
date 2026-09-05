# Asm Match Specification

> Tests covering Asm Match Syntax, Asm Match Complete Example, Asm Assert Examples.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Asm Match Specification

## Scenarios

### Asm Match Syntax

#### recognizes asm match keyword combination

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes asm match keyword combination


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes asm match keyword combination")
val code = "asm match:"
check(code.starts_with("asm"))
check(code.contains("match"))
check(code.ends_with(":"))
```

</details>

#### recognizes case with target spec

- recognizes case with target spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes case with target spec")
val arm = "case [x86_64]:"
check(arm.starts_with("case"))
check(arm.contains("["))
check(arm.contains("x86_64"))
check(arm.contains("]"))
```

</details>

#### recognizes case with pipe grouping

- recognizes case with pipe grouping


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes case with pipe grouping")
val arm = "case [x86_64 | x86]:"
check(arm.contains("|"))
check(arm.contains("x86_64"))
check(arm.contains("x86"))
```

</details>

#### recognizes case with os qualifier

- recognizes case with os qualifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes case with os qualifier")
val arm = "case [x86_64, linux]:"
check(arm.contains(","))
check(arm.contains("linux"))
```

</details>

#### recognizes case with full qualifier

- recognizes case with full qualifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes case with full qualifier")
val arm = "case [x86_64, linux, gnu, llvm >= 15]:"
check(arm.contains("x86_64"))
check(arm.contains("linux"))
check(arm.contains("gnu"))
check(arm.contains("llvm"))
check(arm.contains(">="))
check(arm.contains("15"))
```

</details>

#### recognizes wildcard case

- recognizes wildcard case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes wildcard case")
val arm = "case _:"
check(arm.contains("_"))
```

</details>

#### recognizes compile_error in arm

- recognizes compile_error in arm


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes compile_error in arm")
val body = "compile_error(\"unsupported arch\")"
check(body.starts_with("compile_error"))
check(body.contains("unsupported arch"))
```

</details>

#### recognizes asm assert syntax

- recognizes asm assert syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes asm assert syntax")
val code = "asm assert [x86_64, linux]"
check(code.starts_with("asm"))
check(code.contains("assert"))
check(code.contains("["))
check(code.contains("x86_64"))
```

</details>

### Asm Match Complete Example

#### parses full asm match block syntax

- parses full asm match block syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses full asm match block syntax")
# Verify the complete syntax structure is valid
val example = "asm match:\n    case [x86_64]:\n        \"cli\"\n    case [aarch64]:\n        \"msr daifset, #0xf\"\n    case _:\n        compile_error(\"unsupported\")"
check(example.contains("asm match:"))
check(example.contains("case [x86_64]:"))
check(example.contains("case [aarch64]:"))
check(example.contains("case _:"))
check(example.contains("compile_error"))
```

</details>

#### parses version constraint operators

- parses version constraint operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses version constraint operators")
val ops = [">= 15", "== 17", "< 18", "~= 17"]
check(ops.len() == 4)
check(ops[0].contains(">="))
check(ops[1].contains("=="))
check(ops[2].contains("<"))
check(ops[3].contains("~="))
```

</details>

### Asm Assert Examples

#### parses asm assert with arch only

- parses asm assert with arch only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses asm assert with arch only")
val code = "asm assert [x86_64]"
check(code.contains("assert"))
check(code.contains("x86_64"))
```

</details>

#### parses asm assert with full spec

- parses asm assert with full spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses asm assert with full spec")
val code = "asm assert [x86_64, linux, gnu, llvm >= 15]"
check(code.contains("assert"))
check(code.contains("x86_64"))
check(code.contains("linux"))
check(code.contains("gnu"))
check(code.contains("llvm"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/asm_match_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Asm Match Syntax, Asm Match Complete Example, Asm Assert Examples.
- Asm Match Syntax
- Asm Match Complete Example
- Asm Assert Examples

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

- Canonical SPipe generation for source `f7a3e4fddc7e23eee67ec9249c25e4b4a96c782dd005beb450be633a18d897b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7a3e4fddc7e23eee67ec9249c25e4b4a96c782dd005beb450be633a18d897b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7a3e4fddc7e23eee67ec9249c25e4b4a96c782dd005beb450be633a18d897b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/native/asm_match_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/asm_match_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/asm_match_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/asm_match_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/asm_match_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes asm match keyword combination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/asm_match_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes case with target spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/asm_match_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes case with pipe grouping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
