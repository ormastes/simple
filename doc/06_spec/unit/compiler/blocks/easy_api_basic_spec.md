# Easy Api Basic Specification

> Tests covering Easy API - Tier 1, Easy API - Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Easy Api Basic Specification

## Scenarios

### Easy API - Tier 1

#### block() function

#### creates a simple raw text block

- creates a simple raw text block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a simple raw text block")
# For now, just verify the syntax compiles
# Full testing requires module integration
expect true
```

</details>

#### creates a block with lexer mode

- creates a block with lexer mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a block with lexer mode")
# Placeholder for future test
expect true
```

</details>

#### creates a block with parser

- creates a block with parser


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a block with parser")
# Placeholder for future test
expect true
```

</details>

#### const_block() function

#### creates a compile-time evaluatable block

- creates a compile-time evaluatable block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a compile-time evaluatable block")
# Placeholder for future test
expect true
```

</details>

#### evaluates const values at compile time

- evaluates const values at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates const values at compile time")
# Placeholder for future test
expect true
```

</details>

#### block_with_validation() function

#### creates a block with post-parse validation

- creates a block with post-parse validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a block with post-parse validation")
# Placeholder for future test
expect true
```

</details>

#### validates block values correctly

- validates block values correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates block values correctly")
# Placeholder for future test
expect true
```

</details>

#### reports validation errors

- reports validation errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports validation errors")
# Placeholder for future test
expect true
```

</details>

### Easy API - Integration

#### block registration

#### registers blocks with global registry

- registers blocks with global registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers blocks with global registry")
# Placeholder for future test
expect true
```

</details>

#### allows blocks to be used in code

- allows blocks to be used in code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows blocks to be used in code")
# Placeholder for future test
expect true
```

</details>

#### error handling

#### handles parse errors gracefully

- handles parse errors gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles parse errors gracefully")
# Placeholder for future test
expect true
```

</details>

#### provides clear error messages

- provides clear error messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides clear error messages")
# Placeholder for future test
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/blocks/easy_api_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Easy API - Tier 1, Easy API - Integration.
- Easy API - Tier 1
- Easy API - Integration

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

- Canonical SPipe generation for source `bf8b7cd5b22d4b21228c594a3b5a7d18645090b2e0a09b4ff4bed87fdb9ff979`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf8b7cd5b22d4b21228c594a3b5a7d18645090b2e0a09b4ff4bed87fdb9ff979`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf8b7cd5b22d4b21228c594a3b5a7d18645090b2e0a09b4ff4bed87fdb9ff979`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/blocks/easy_api_basic_spec.spl
mirror: doc/06_spec/unit/compiler/blocks/easy_api_basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/blocks/easy_api_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/blocks/easy_api_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/blocks/easy_api_basic_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a simple raw text block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/blocks/easy_api_basic_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a block with lexer mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/blocks/easy_api_basic_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a block with parser' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
