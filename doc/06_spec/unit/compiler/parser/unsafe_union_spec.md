# Unsafe Union Specification

> Tests covering union types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsafe Union Specification

## Scenarios

### union types

#### type-OR union via pipe syntax parses correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- type-OR union via pipe syntax parses correctly
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type-OR union via pipe syntax parses correctly")
# i64 | text | bool  - this is the Type-OR union syntax
# Stored as separate types, resolved at runtime
val x: i64 = 42
expect(x).to_equal(42)
```

</details>

#### function accepting multiple types via union

- function accepting multiple types via union
   - Expected: result equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function accepting multiple types via union")
val result = parse_number_or_text("123")
expect(result).to_equal(123)
```

</details>

#### match on union-typed value works

- match on union-typed value works
   - Expected: category equals `negative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match on union-typed value works")
val n: i64 = -5
val category = classify_value(n)
expect(category).to_equal("negative")
```

</details>

#### positive value classified correctly

- positive value classified correctly
   - Expected: category equals `positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive value classified correctly")
val n: i64 = 10
val category = classify_value(n)
expect(category).to_equal("positive")
```

</details>

#### zero value classified correctly

- zero value classified correctly
   - Expected: category equals `zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero value classified correctly")
val n: i64 = 0
val category = classify_value(n)
expect(category).to_equal("zero")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/unsafe_union_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering union types.
- union types

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

- Canonical SPipe generation for source `df56a8ca49eeab9d296fd4a8af594fe60bc49a43c52ccd71e2cd3747cf77e209`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df56a8ca49eeab9d296fd4a8af594fe60bc49a43c52ccd71e2cd3747cf77e209`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df56a8ca49eeab9d296fd4a8af594fe60bc49a43c52ccd71e2cd3747cf77e209`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/parser/unsafe_union_spec.spl
mirror: doc/06_spec/unit/compiler/parser/unsafe_union_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/unsafe_union_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/unsafe_union_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/unsafe_union_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/unsafe_union_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'type-OR union via pipe syntax parses correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/unsafe_union_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function accepting multiple types via union' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/unsafe_union_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'match on union-typed value works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
