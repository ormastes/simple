# Optional Nested Aggregate Retention Specification

> Tests covering optional nested aggregate survives a module-global round trip, detection: the loss is specific to the NESTED optional, not the class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optional Nested Aggregate Retention Specification

## Scenarios

### optional nested aggregate survives a module-global round trip

#### the JIT reads back the nested blob instead of faulting

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the JIT reads back the nested blob instead of faulting


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the JIT reads back the nested blob instead of faulting")
assert_contains(_out("jit"), "blob_len=3")
```

</details>

### detection: the loss is specific to the NESTED optional, not the class

#### the flat scalar field round-trips on both engines

- the flat scalar field round-trips on both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the flat scalar field round-trips on both engines")
assert_contains(_out("jit"), "name=a")
assert_contains(_out("interpreter"), "name=a")
```

</details>

#### the interpreter is the correct reference for the nested blob

- the interpreter is the correct reference for the nested blob


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the interpreter is the correct reference for the nested blob")
assert_contains(_out("interpreter"), "blob_len=3")
```

</details>

#### the read-back never reports the optional as nil

- the read-back never reports the optional as nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the read-back never reports the optional as nil")
assert_true(not _out("jit").contains("blob_len=NIL"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering optional nested aggregate survives a module-global round trip, detection: the loss is specific to the NESTED optional, not the class.
- optional nested aggregate survives a module-global round trip
- detection: the loss is specific to the NESTED optional, not the class

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

- Canonical SPipe generation for source `22952dcf84e70452d06a70ac24f48a6d2a4fd925b3a32a3517ed4cc5bd040cc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22952dcf84e70452d06a70ac24f48a6d2a4fd925b3a32a3517ed4cc5bd040cc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22952dcf84e70452d06a70ac24f48a6d2a4fd925b3a32a3517ed4cc5bd040cc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.spl
mirror: doc/06_spec/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the JIT reads back the nested blob instead of faulting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the flat scalar field round-trips on both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/text_layout/optional_nested_aggregate_retention_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the interpreter is the correct reference for the nested blob' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
