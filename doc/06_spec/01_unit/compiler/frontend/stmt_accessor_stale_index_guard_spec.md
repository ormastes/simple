# Stmt Accessor Stale Index Guard Specification

> Tests covering statement accessors on an index stale across an arena reset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stmt Accessor Stale Index Guard Specification

## Scenarios

### statement accessors on an index stale across an arena reset

#### returns the -1 no-tag sentinel from stmt_get_tag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the -1 no-tag sentinel from stmt_get_tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the -1 no-tag sentinel from stmt_get_tag")
expect stmt_get_tag(_stale_index()) to_equal -1
```

</details>

#### returns -1 from stmt_get_span instead of aborting the process

- returns -1 from stmt_get_span instead of aborting the process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 from stmt_get_span instead of aborting the process")
expect stmt_get_span(_stale_index()) to_equal -1
```

</details>

#### returns -1 from stmt_get_expr instead of aborting the process

- returns -1 from stmt_get_expr instead of aborting the process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 from stmt_get_expr instead of aborting the process")
expect stmt_get_expr(_stale_index()) to_equal -1
```

</details>

#### returns the empty name from stmt_get_name instead of aborting

- returns the empty name from stmt_get_name instead of aborting


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the empty name from stmt_get_name instead of aborting")
expect stmt_get_name(_stale_index()) to_equal ""
```

</details>

#### returns -1 from stmt_get_type instead of aborting the process

- returns -1 from stmt_get_type instead of aborting the process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 from stmt_get_type instead of aborting the process")
expect stmt_get_type(_stale_index()) to_equal -1
```

</details>

#### returns an empty body list from stmt_get_body instead of aborting

- returns an empty body list from stmt_get_body instead of aborting


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty body list from stmt_get_body instead of aborting")
expect stmt_get_body(_stale_index()).len() to_equal 0
```

</details>

#### still reads a LIVE index correctly -- the guard is not a blanket -1

- still reads a LIVE index correctly -- the guard is not a blanket -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reads a LIVE index correctly -- the guard is not a blanket -1")
stmt_reset()
val live = stmt_alloc(STMT_EXPR, 7)
expect stmt_get_tag(live) to_equal STMT_EXPR
expect stmt_get_span(live) to_equal 7
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering statement accessors on an index stale across an arena reset.
- statement accessors on an index stale across an arena reset

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

- Canonical SPipe generation for source `88c5779982b016e52361f6545bdef364667ce76b68d8386e5634973733b0bb05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88c5779982b016e52361f6545bdef364667ce76b68d8386e5634973733b0bb05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88c5779982b016e52361f6545bdef364667ce76b68d8386e5634973733b0bb05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the -1 no-tag sentinel from stmt_get_tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns -1 from stmt_get_span instead of aborting the process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns -1 from stmt_get_expr instead of aborting the process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
