# Safety Visibility Specification

> Tests covering Safety and Visibility Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safety Visibility Specification

## Scenarios

### Safety and Visibility Lint

#### private symbol imports

#### flags importing _private_fn from another module (W0401)

- flags importing _private_fn from another module (W0401)
   - Expected: has_w0401 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags importing _private_fn from another module (W0401)")
val code = 'use std.nogc_sync_mut.fs.{_private_helper}' + "\n\nfn test():\n    print \"test\"\n"
val codes = check_visibility_text(code)
val has_w0401 = codes_contain(codes, "W0401")
expect(has_w0401).to_equal(true)
```

</details>

#### flags importing _internal symbol

- flags importing _internal symbol
   - Expected: has_w0401 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags importing _internal symbol")
val code = 'use std.common.text.{_internal_parse}' + "\n\nfn test():\n    print \"test\"\n"
val codes = check_visibility_text(code)
val has_w0401 = codes_contain(codes, "W0401")
expect(has_w0401).to_equal(true)
```

</details>

#### public symbol imports

#### does not flag importing public symbols

- does not flag importing public symbols
   - Expected: has_w0401 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag importing public symbols")
val code = "use std.spec\n\nfn test():\n    print \"test\"\n"
val codes = check_visibility_text(code)
val has_w0401 = codes_contain(codes, "W0401")
expect(has_w0401).to_equal(false)
```

</details>

#### asm outside unsafe

#### flags asm usage outside unsafe block (SAFE001)

- flags asm usage outside unsafe block (SAFE001)
   - Expected: has_safe001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags asm usage outside unsafe block (SAFE001)")
val code = "fn test():\n    asm \"nop\"\n"
val codes = check_safety_text(code)
val has_safe001 = codes_contain(codes, "SAFE001")
expect(has_safe001).to_equal(true)
```

</details>

#### flags standalone asm on indented line

- flags standalone asm on indented line
   - Expected: has_safe001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags standalone asm on indented line")
val code = "fn compute():\n    asm \"mov eax, 42\"\n    print \"done\"\n"
val codes = check_safety_text(code)
val has_safe001 = codes_contain(codes, "SAFE001")
expect(has_safe001).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/lint/safety_visibility_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Safety and Visibility Lint.
- Safety and Visibility Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `6cf93d7c4db443e37e7701b2e38f7083e3b0bbf150f84e961a00f09d087a48fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6cf93d7c4db443e37e7701b2e38f7083e3b0bbf150f84e961a00f09d087a48fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6cf93d7c4db443e37e7701b2e38f7083e3b0bbf150f84e961a00f09d087a48fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/semantics/lint/safety_visibility_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/lint/safety_visibility_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/lint/safety_visibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/lint/safety_visibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/lint/safety_visibility_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags importing _private_fn from another module (W0401)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/lint/safety_visibility_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags importing _internal symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/lint/safety_visibility_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag importing public symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
