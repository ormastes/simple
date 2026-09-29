# Treesitter Query Specification

> Tests covering Query Creation, Query Execution, QueryCursor.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Query Specification

## Scenarios

### Query Creation

#### creates query for Simple language

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates query for Simple language


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates query for Simple language")
val query = MockQuery.new("(identifier) @name")
check(query.pattern.len() > 0)
```

</details>

#### handles invalid query

- handles invalid query


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles invalid query")
val query = MockQuery.new("invalid pattern")
check(query.pattern.len() > 0)
```

</details>

### Query Execution

#### matches patterns

- matches patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches patterns")
val query = MockQuery.new("(identifier)")
check(query.execute())
```

</details>

#### captures nodes

- captures nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures nodes")
val query = MockQuery.new("(identifier) @var")
val captures = query.get_captures()
check(captures.len() > 0)
```

</details>

#### supports predicates

- supports predicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports predicates")
val query = MockQuery.new("(function_definition) @func")
check(query.execute())
```

</details>

### QueryCursor

#### iterates matches

- iterates matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates matches")
val cursor = MockQueryCursor.new()
check(cursor.next_match())
```

</details>

#### supports byte range

- supports byte range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports byte range")
val cursor = MockQueryCursor.new()
check(cursor.supports_byte_range())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_query_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Query Creation, Query Execution, QueryCursor.
- Query Creation
- Query Execution
- QueryCursor

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

- Canonical SPipe generation for source `27231b80b867962d2499642b624b7df5224907087d80da1f10870b8cc15c33bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27231b80b867962d2499642b624b7df5224907087d80da1f10870b8cc15c33bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27231b80b867962d2499642b624b7df5224907087d80da1f10870b8cc15c33bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/treesitter_query_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/treesitter_query_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/treesitter_query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/treesitter_query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/treesitter_query_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates query for Simple language' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/treesitter_query_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles invalid query' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/treesitter_query_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
