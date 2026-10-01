# Unreachable Code Specification

> Tests covering Unreachable Code Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unreachable Code Specification

## Scenarios

### Unreachable Code Lint

#### code after return

#### flags code after return statement

- flags code after return statement
   - Expected: has_warning is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags code after return statement")
val code = "fn test() -> i64:\n    return 42\n    val x = 10\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(true)
```

</details>

#### flags code after return with value

- flags code after return with value
   - Expected: has_warning is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags code after return with value")
val code = "fn compute() -> text:\n    return \"done\"\n    print \"never reached\"\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(true)
```

</details>

#### unreachable code has UNREACH001 code

- unreachable code has UNREACH001 code
   - Expected: has_code is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unreachable code has UNREACH001 code")
val code = "fn test() -> i64:\n    return 1\n    val dead = 2\n"
val codes = check_unreachable_text(code)
val has_code = codes_contain(codes, "UNREACH001")
expect(has_code).to_equal(true)
```

</details>

#### reachable code

#### does not flag code before return

- does not flag code before return
   - Expected: has_warning is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag code before return")
val code = "fn test() -> i64:\n    val x = 10\n    return x\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag code in different branches

- does not flag code in different branches
   - Expected: has_warning is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag code in different branches")
val code = "fn test(flag: bool) -> i64:\n    if flag:\n        return 1\n    return 0\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag code after return in nested if

- does not flag code after return in nested if
   - Expected: has_warning is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag code after return in nested if")
val code = "fn test(x: i64) -> text:\n    if x > 0:\n        return \"positive\"\n    \"non-positive\"\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag empty function body

- does not flag empty function body
   - Expected: has_warning is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag empty function body")
val code = "fn noop():\n    pass_do_nothing\n"
val codes = check_unreachable_text(code)
val has_warning = codes_contain(codes, "UNREACH001")
expect(has_warning).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/unreachable_code_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Unreachable Code Lint.
- Unreachable Code Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `09dd1deeb48eb3197792ea212c0004e244a4487be3d885863044bd3ed1c16f8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09dd1deeb48eb3197792ea212c0004e244a4487be3d885863044bd3ed1c16f8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09dd1deeb48eb3197792ea212c0004e244a4487be3d885863044bd3ed1c16f8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/lint/unreachable_code_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/unreachable_code_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/unreachable_code_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/unreachable_code_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/unreachable_code_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags code after return statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/unreachable_code_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags code after return with value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/unreachable_code_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unreachable code has UNREACH001 code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
