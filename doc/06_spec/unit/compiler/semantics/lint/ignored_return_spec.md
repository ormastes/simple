# Ignored Return Specification

> Tests covering Ignored Return Value Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ignored Return Specification

## Scenarios

### Ignored Return Value Lint

#### discarded return values

#### flags discarded return value from pure function (RET001)

- flags discarded return value from pure function (RET001)
   - Expected: has_ret001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags discarded return value from pure function (RET001)")
val code = "fn compute() -> i64:\n    42\n\nfn test():\n    compute()\n    print \"done\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(true)
```

</details>

#### flags discarded string return

- flags discarded string return
   - Expected: has_ret001 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags discarded string return")
val code = "fn get_name() -> text:\n    \"Alice\"\n\nfn test():\n    get_name()\n    print \"done\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(true)
```

</details>

#### side-effectful functions

#### does not flag print calls

- does not flag print calls
   - Expected: has_ret001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag print calls")
val code = "fn test():\n    print \"hello\"\n    print \"world\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

#### does not flag push calls

- does not flag push calls
   - Expected: has_ret001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag push calls")
val code = "fn test():\n    var items: [text] = []\n    items.push(\"hello\")\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

#### implicit return (last expression)

#### does not flag last expression as implicit return

- does not flag last expression as implicit return
   - Expected: has_ret001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag last expression as implicit return")
val code = "fn compute() -> i64:\n    val x = 10\n    x * 2\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

#### does not flag last expression in function with return type

- does not flag last expression in function with return type
   - Expected: has_ret001 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag last expression in function with return type")
val code = "fn greet(name: text) -> text:\n    \"Hello!\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/lint/ignored_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ignored Return Value Lint.
- Ignored Return Value Lint

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a9c4645921bcad1d6ddc2fab7ee9912a58211bf33ed4df7796a53a4a3c0ae29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a9c4645921bcad1d6ddc2fab7ee9912a58211bf33ed4df7796a53a4a3c0ae29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a9c4645921bcad1d6ddc2fab7ee9912a58211bf33ed4df7796a53a4a3c0ae29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/semantics/lint/ignored_return_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/lint/ignored_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/lint/ignored_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/lint/ignored_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/lint/ignored_return_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags discarded return value from pure function (RET001)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/lint/ignored_return_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags discarded string return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/lint/ignored_return_spec.spl:170:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag print calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
