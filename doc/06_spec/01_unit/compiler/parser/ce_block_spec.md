# Ce Block Specification

> Tests covering ce block syntax - basic concepts, ce block syntax - bind statement, ce block syntax - builder names, ce block syntax - final expression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ce Block Specification

## Scenarios

### ce block syntax - basic concepts

#### ce block equivalent with single bind evaluates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ce block equivalent with single bind evaluates
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ce block equivalent with single bind evaluates")
# Equivalent of: ce result_ce: bind x = 42; x
val x = 42
expect(x).to_equal(42)
```

</details>

#### ce block equivalent returns last expression value

- ce block equivalent returns last expression value
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ce block equivalent returns last expression value")
# Equivalent of: ce option_ce: bind a = 10; bind b = 20; a + b
val a = 10
val b = 20
val result = a + b
expect(result).to_equal(30)
```

</details>

#### ce block equivalent with text bind

- ce block equivalent with text bind
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ce block equivalent with text bind")
val name = "hello"
val result = name
expect(result).to_equal("hello")
```

</details>

### ce block syntax - bind statement

#### bind x = expr makes x available in rest of block

- bind x = expr makes x available in rest of block
   - Expected: second equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bind x = expr makes x available in rest of block")
val first = 5
val second = first * 2
expect(second).to_equal(10)
```

</details>

#### multiple bind statements chain

- multiple bind statements chain
   - Expected: result equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("multiple bind statements chain")
val a = 1
val b = 2
val c = 3
val result = a + b + c
expect(result).to_equal(6)
```

</details>

#### bind name is accessible after bind statement

- bind name is accessible after bind statement
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bind name is accessible after bind statement")
val item = "world"
val result = "hello " + item
expect(result).to_equal("hello world")
```

</details>

### ce block syntax - builder names

#### result_ce builder concept

- result_ce builder concept
   - Expected: x equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("result_ce builder concept")
val x = 99
expect(x).to_equal(99)
```

</details>

#### option_ce builder concept

- option_ce builder concept
   - Expected: result equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("option_ce builder concept")
val x = 7
val result = x * 3
expect(result).to_equal(21)
```

</details>

#### custom_ce builder concept

- custom_ce builder concept
   - Expected: x equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("custom_ce builder concept")
val x = 100
expect(x).to_equal(100)
```

</details>

### ce block syntax - final expression

#### final expression is the return value

- final expression is the return value
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("final expression is the return value")
val result = 100
expect(result).to_equal(100)
```

</details>

#### final expression after binds is the return value

- final expression after binds is the return value
   - Expected: result equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("final expression after binds is the return value")
val a = 5
val b = 10
val result = a * b
expect(result).to_equal(50)
```

</details>

#### final text expression after bind

- final text expression after bind
   - Expected: result equals `pre_suf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("final text expression after bind")
val prefix = "pre"
val suffix = "suf"
val result = prefix + "_" + suffix
expect(result).to_equal("pre_suf")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/ce_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ce block syntax - basic concepts, ce block syntax - bind statement, ce block syntax - builder names, ce block syntax - final expression.
- ce block syntax - basic concepts
- ce block syntax - bind statement
- ce block syntax - builder names
- ce block syntax - final expression

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `90c29c19480405906104ca81fb2d34e1f569706c8127488a76c539b15d823d47`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90c29c19480405906104ca81fb2d34e1f569706c8127488a76c539b15d823d47`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90c29c19480405906104ca81fb2d34e1f569706c8127488a76c539b15d823d47`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/parser/ce_block_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/ce_block_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/ce_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/ce_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/ce_block_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/ce_block_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ce block equivalent with single bind evaluates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/ce_block_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ce block equivalent returns last expression value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/ce_block_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ce block equivalent with text bind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
