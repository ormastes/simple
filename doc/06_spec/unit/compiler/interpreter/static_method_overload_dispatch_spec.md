# Static Method Overload Dispatch Specification

> Tests covering interpreter static method overload dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Method Overload Dispatch Specification

## Scenarios

### interpreter static method overload dispatch

#### selects the inline static overload for i64 arguments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects the inline static overload for i64 arguments
   - Expected: InlineStaticOverload.select(value) equals `inline-i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects the inline static overload for i64 arguments")
var value: i64 = 7
expect(InlineStaticOverload.select(value)).to_equal("inline-i64")
```

</details>

#### selects the inline static overload for text arguments

- selects the inline static overload for text arguments
   - Expected: InlineStaticOverload.select(value) equals `inline-text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects the inline static overload for text arguments")
var value: text = "hello"
expect(InlineStaticOverload.select(value)).to_equal("inline-text")
```

</details>

#### selects the impl-defined static overload for i64 arguments

- selects the impl-defined static overload for i64 arguments
   - Expected: ImplStaticOverload.select(value) equals `impl-i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects the impl-defined static overload for i64 arguments")
var value: i64 = 9
expect(ImplStaticOverload.select(value)).to_equal("impl-i64")
```

</details>

#### selects the impl-defined static overload for text arguments

- selects the impl-defined static overload for text arguments
   - Expected: ImplStaticOverload.select(value) equals `impl-text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects the impl-defined static overload for text arguments")
var value: text = "world"
expect(ImplStaticOverload.select(value)).to_equal("impl-text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/interpreter/static_method_overload_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter static method overload dispatch.
- interpreter static method overload dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `ad2ce5c7fdcce13f2a54b1379644f2ad14326cf34b7fba20d04a1190dadc5ad5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad2ce5c7fdcce13f2a54b1379644f2ad14326cf34b7fba20d04a1190dadc5ad5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad2ce5c7fdcce13f2a54b1379644f2ad14326cf34b7fba20d04a1190dadc5ad5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/interpreter/static_method_overload_dispatch_spec.spl
mirror: doc/06_spec/unit/compiler/interpreter/static_method_overload_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/interpreter/static_method_overload_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/interpreter/static_method_overload_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/interpreter/static_method_overload_dispatch_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects the inline static overload for i64 arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/static_method_overload_dispatch_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects the inline static overload for text arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/static_method_overload_dispatch_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects the impl-defined static overload for i64 arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
