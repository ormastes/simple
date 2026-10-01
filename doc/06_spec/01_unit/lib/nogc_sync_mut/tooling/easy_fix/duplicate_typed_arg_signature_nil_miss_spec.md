# Duplicate Typed Arg Signature Nil Miss Specification

> Tests covering duplicate-typed-args signature parse on the nil-miss path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Typed Arg Signature Nil Miss Specification

## Scenarios

### duplicate-typed-args signature parse on the nil-miss path

#### does not crash lint on a signature with no duplicate parameter types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not crash lint on a signature with no duplicate parameter types
- Lint a function whose params have distinct types


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not crash lint on a signature with no duplicate parameter types")
"""A signature whose parameter types are all distinct must be parsed
as 'no match' (nil), not crash the non-optional return contract."""
step("Lint a function whose params have distinct types")
var count = 0
for result in lint_cli_source(Linter.new(), "/tmp/dtyp_nil_miss_no_dup.spl", NO_DUP_SRC):
    if result.lint.code == "DTYP001":
        count = count + 1
assert_equal(count, 0)
```

</details>

#### does not crash lint on a signature with fewer than two typed params

- does not crash lint on a signature with fewer than two typed params
- Lint a function with only one parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not crash lint on a signature with fewer than two typed params")
"""A single-parameter signature must also resolve to nil cleanly."""
step("Lint a function with only one parameter")
var count = 0
for result in lint_cli_source(Linter.new(), "/tmp/dtyp_nil_miss_single.spl", SINGLE_ARG_SRC):
    if result.lint.code == "DTYP001":
        count = count + 1
assert_equal(count, 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering duplicate-typed-args signature parse on the nil-miss path.
- duplicate-typed-args signature parse on the nil-miss path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `75939a28a552b65f3f3a265584d8dd7961836ba187967a4d95d281bb79d51ae7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75939a28a552b65f3f3a265584d8dd7961836ba187967a4d95d281bb79d51ae7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75939a28a552b65f3f3a265584d8dd7961836ba187967a4d95d281bb79d51ae7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not crash lint on a signature with no duplicate parameter types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not crash lint on a signature with fewer than two typed params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
