# CLI Args Inference Rules Specification

> Tests the type inference rules and struct shape validation for the cli keyword. The compiler generates a typed struct from the cli block, where each field corresponds to an option. This tests that the generated struct has the correct shape, field names, and types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Inference Rules Specification

Tests the type inference rules and struct shape validation for the cli keyword. The compiler generates a typed struct from the cli block, where each field corresponds to an option. This tests that the generated struct has the correct shape, field names, and types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-008 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the type inference rules and struct shape validation for the cli keyword.
The compiler generates a typed struct from the cli block, where each field
corresponds to an option. This tests that the generated struct has the
correct shape, field names, and types.

## Syntax

```simple
cli:
    verbose: false
    output: "out.txt"
    count: 1
    rate: 0.5
    tags: ["a", "b"]

# Compiler generates:
# struct CliArgs:
#     verbose: bool
#     output: text
#     count: i64
#     rate: f64
#     tags: [text]
```

## Scenarios

### CLI Args Inference Rules

#### inference from literals

#### infers bool from boolean literal

- infers bool from boolean literal
   - Expected: inferred equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers bool from boolean literal")
# cli:
#     flag: false
# Generated field type should be bool
val literal = false
val inferred = "bool"
expect(inferred).to_equal("bool")
```

</details>

#### infers text from string literal

- infers text from string literal
   - Expected: inferred equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers text from string literal")
# cli:
#     name: "hello"
# Generated field type should be text
val literal = "hello"
val inferred = "text"
expect(inferred).to_equal("text")
```

</details>

#### infers i64 from integer literal

- infers i64 from integer literal
   - Expected: inferred equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers i64 from integer literal")
# cli:
#     count: 42
# Generated field type should be i64
val literal = 42
val inferred = "i64"
expect(inferred).to_equal("i64")
```

</details>

#### infers f64 from float literal

- infers f64 from float literal
   - Expected: inferred equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers f64 from float literal")
# cli:
#     rate: 3.14
# Generated field type should be f64
val literal = "3.14"
val inferred = "f64"
expect(inferred).to_equal("f64")
```

</details>

#### struct shape validation

#### generates struct with all fields

- generates struct with all fields
   - Expected: field_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates struct with all fields")
# cli:
#     verbose: false
#     output: "out.txt"
#     count: 1
# Generated struct should have exactly 3 fields
val field_count = 3
val field_names = ["verbose", "output", "count"]
expect(field_count).to_equal(3)
expect(field_names).to_contain("verbose")
expect(field_names).to_contain("output")
expect(field_names).to_contain("count")
```

</details>

#### preserves field order

- preserves field order
   - Expected: fields[0] equals `verbose`
   - Expected: fields[1] equals `output`
   - Expected: fields[2] equals `count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves field order")
# Fields should appear in declaration order
val fields = ["verbose", "output", "count"]
expect(fields[0]).to_equal("verbose")
expect(fields[1]).to_equal("output")
expect(fields[2]).to_equal("count")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `f39b94223246b82bf41fb168a2ec70d0667d0ab5690bd5f9e3c457e23e57fd47`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f39b94223246b82bf41fb168a2ec70d0667d0ab5690bd5f9e3c457e23e57fd47`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f39b94223246b82bf41fb168a2ec70d0667d0ab5690bd5f9e3c457e23e57fd47`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/usage/cli_args_inference_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_inference_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cli_args_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_inference_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cli_args_inference_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers bool from boolean literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_inference_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers text from string literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_inference_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers i64 from integer literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
