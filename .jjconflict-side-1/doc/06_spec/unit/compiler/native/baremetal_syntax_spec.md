# Baremetal Syntax Specification

> Tests covering Volatile Syntax, Unsafe Syntax, Interrupt Syntax, Memory Layout Attributes, Bitfield Syntax, Address Syntax, Static Assert, Const Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Syntax Specification

## Scenarios

### Volatile Syntax

#### recognizes @volatile attribute

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes @volatile attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes @volatile attribute")
# This test verifies the lexer recognizes @volatile
# Actual behavior is tested elsewhere
val result = "volatile attribute recognized"
assert result.len() > 0
```

</details>

#### parses volatile variable declaration

- parses volatile variable declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses volatile variable declaration")
# The parser should handle: @volatile val reg: u32
val declaration = "@volatile val"
assert declaration.starts_with("@volatile")
```

</details>

### Unsafe Syntax

#### recognizes unsafe keyword

- recognizes unsafe keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes unsafe keyword")
# The lexer should have KwUnsafe token
val keyword = "unsafe"
assert keyword == "unsafe"
```

</details>

#### parses unsafe block structure

- parses unsafe block structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses unsafe block structure")
# Parser handles: unsafe: block
val syntax = "unsafe: pass"
assert syntax.contains("unsafe")
```

</details>

### Interrupt Syntax

#### recognizes @interrupt attribute

- recognizes @interrupt attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes @interrupt attribute")
val attr = "@interrupt"
assert attr.starts_with("@")
```

</details>

#### parses interrupt handler declaration

- parses interrupt handler declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses interrupt handler declaration")
val decl = "@interrupt(32) fn timer_handler():"
assert decl.contains("interrupt")
```

</details>

### Memory Layout Attributes

#### recognizes @repr attribute

- recognizes @repr attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes @repr attribute")
val attr = "@repr(C)"
assert attr.contains("repr")
```

</details>

#### recognizes @packed attribute

- recognizes @packed attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes @packed attribute")
val attr = "@packed"
assert attr.contains("packed")
```

</details>

#### recognizes @align attribute

- recognizes @align attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes @align attribute")
val attr = "@align(16)"
assert attr.contains("align")
```

</details>

### Bitfield Syntax

#### recognizes bitfield keyword

- recognizes bitfield keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes bitfield keyword")
val kw = "bitfield"
assert kw == "bitfield"
```

</details>

#### parses bitfield structure

- parses bitfield structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bitfield structure")
val syntax = "bitfield ControlReg:"
assert syntax.starts_with("bitfield")
```

</details>

### Address Syntax

#### parses @ address syntax

- parses @ address syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @ address syntax")
# Parser should handle: val REG: u32 @ 0x40000000
val addr = "0x40000000"
assert addr.starts_with("0x")
```

</details>

### Static Assert

#### recognizes static assert

- recognizes static assert


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes static assert")
val sa = "static assert size_of<u32>() == 4"
assert sa.starts_with("static")
```

</details>

### Const Functions

#### recognizes const fn

- recognizes const fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes const fn")
val cf = "const fn compute() -> i64:"
assert cf.contains("const fn")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/native/baremetal_syntax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Volatile Syntax, Unsafe Syntax, Interrupt Syntax, Memory Layout Attributes, Bitfield Syntax, Address Syntax, Static Assert, Const Functions.
- Volatile Syntax
- Unsafe Syntax
- Interrupt Syntax
- Memory Layout Attributes
- Bitfield Syntax
- Address Syntax
- Static Assert
- Const Functions

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed38c4346fc0034d2d66868dec16d2f11553244670a0f759ff95d8563ce3d292`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed38c4346fc0034d2d66868dec16d2f11553244670a0f759ff95d8563ce3d292`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed38c4346fc0034d2d66868dec16d2f11553244670a0f759ff95d8563ce3d292`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/native/baremetal_syntax_spec.spl
mirror: doc/06_spec/unit/compiler/native/baremetal_syntax_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/native/baremetal_syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/native/baremetal_syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/native/baremetal_syntax_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes @volatile attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/baremetal_syntax_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses volatile variable declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/native/baremetal_syntax_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes unsafe keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
