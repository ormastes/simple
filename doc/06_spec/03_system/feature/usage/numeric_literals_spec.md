# Numeric Literals Specification

> Tests for various numeric literal formats including hexadecimal, binary, octal, and numeric separators with underscores.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Literals Specification

Tests for various numeric literal formats including hexadecimal, binary, octal, and numeric separators with underscores.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NUM-001 |
| Category | Language \| Literals |
| Status | Implemented |
| Source | `test/03_system/feature/usage/numeric_literals_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for various numeric literal formats including hexadecimal, binary,
octal, and numeric separators with underscores.

## Syntax

```simple
use std.spec.step

val hex = 0xFF         # Hexadecimal (255)
val bin = 0b1010       # Binary (10)
val oct = 0o755        # Octal (493)
val sep = 1_000_000    # Underscores for readability
```

## Scenarios

### Hexadecimal Literals

#### parses basic hex literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses basic hex literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses basic hex literal")
val x = 0xFF
expect x == 255
```

</details>

#### parses lowercase hex

- parses lowercase hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses lowercase hex")
val x = 0xff
expect x == 255
```

</details>

#### parses mixed case hex

- parses mixed case hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses mixed case hex")
val x = 0xAb
expect x == 171
```

</details>

#### performs hex arithmetic

- performs hex arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("performs hex arithmetic")
val x = 0x10 + 0x20
expect x == 48  # 16 + 32
```

</details>

#### compares hex and decimal

- compares hex and decimal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares hex and decimal")
expect 0x10 == 16
expect 0x100 == 256
```

</details>

### Binary Literals

#### parses basic binary literal

- parses basic binary literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses basic binary literal")
val x = 0b1010
expect x == 10
```

</details>

#### parses binary with underscores

- parses binary with underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses binary with underscores")
val x = 0b1111_0000
expect x == 240
```

</details>

#### performs binary arithmetic

- performs binary arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("performs binary arithmetic")
val x = 0b1000 + 0b0100
expect x == 12  # 8 + 4
```

</details>

#### uses binary for bit patterns

- uses binary for bit patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses binary for bit patterns")
val flags = 0b0101
expect flags == 5
```

</details>

### Octal Literals

#### parses basic octal literal

- parses basic octal literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses basic octal literal")
val x = 0o755
expect x == 493  # 7*64 + 5*8 + 5
```

</details>

#### parses small octal

- parses small octal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses small octal")
val x = 0o10
expect x == 8
```

</details>

#### performs octal arithmetic

- performs octal arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("performs octal arithmetic")
val x = 0o10 + 0o10
expect x == 16  # 8 + 8
```

</details>

### Numeric Separators

#### parses decimal with separators

- parses decimal with separators


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses decimal with separators")
val x = 1_000_000
expect x == 1000000
```

</details>

#### parses hex with separators

- parses hex with separators


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses hex with separators")
val x = 0xFF_FF
expect x == 65535
```

</details>

#### parses binary with separators

- parses binary with separators


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses binary with separators")
val x = 0b1010_1010
expect x == 170
```

</details>

#### allows multiple underscores

- allows multiple underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows multiple underscores")
val x = 100__000
expect x == 100000
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `046e4967fcbb1bfb00086192ab5cdaf81af8f0eb3227b2342d30005e8d62f03e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `046e4967fcbb1bfb00086192ab5cdaf81af8f0eb3227b2342d30005e8d62f03e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `046e4967fcbb1bfb00086192ab5cdaf81af8f0eb3227b2342d30005e8d62f03e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/numeric_literals_spec.spl
mirror: doc/06_spec/03_system/feature/usage/numeric_literals_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/numeric_literals_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/numeric_literals_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/numeric_literals_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses basic hex literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/numeric_literals_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses lowercase hex' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/numeric_literals_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses mixed case hex' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
