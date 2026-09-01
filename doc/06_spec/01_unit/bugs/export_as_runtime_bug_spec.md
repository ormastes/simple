# Export As Runtime Bug Specification

> Tests covering Export As Runtime Bug.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export As Runtime Bug Specification

## Scenarios

### Export As Runtime Bug

#### demonstrates working workaround using wrapper functions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- demonstrates working workaround using wrapper functions
   - Expected: result1 equals `10`
   - Expected: result2 equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("demonstrates working workaround using wrapper functions")
val result1 = aliased_function(5)
val result2 = renamed_function(5)

expect(result1).to_equal(10)
expect(result2).to_equal(15)
```

</details>

#### documents the broken export alias syntax in the fixture

- documents the broken export alias syntax in the fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("documents the broken export alias syntax in the fixture")
val source = export_as_module_source()

expect(source).to_contain("# export original_function as aliased_function")
expect(source).to_contain("# export another_function as renamed_function")
```

</details>

#### documents the active wrapper export used until alias syntax works

- documents the active wrapper export used until alias syntax works


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("documents the active wrapper export used until alias syntax works")
val source = export_as_module_source()

expect(source).to_contain("fn aliased_function(x: i64) -> i64")
expect(source).to_contain("fn renamed_function(x: i64) -> i64")
expect(source).to_contain("export aliased_function, renamed_function")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/export_as_runtime_bug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Export As Runtime Bug.
- Export As Runtime Bug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BUGS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62b2abcbb383652f8916e29233855b5d430eeaf934360e443352b3ce69ecb4a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62b2abcbb383652f8916e29233855b5d430eeaf934360e443352b3ce69ecb4a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62b2abcbb383652f8916e29233855b5d430eeaf934360e443352b3ce69ecb4a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/bugs/export_as_runtime_bug_spec.spl
mirror: doc/06_spec/01_unit/bugs/export_as_runtime_bug_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/export_as_runtime_bug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/export_as_runtime_bug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/export_as_runtime_bug_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/bugs/export_as_runtime_bug_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'demonstrates working workaround using wrapper functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/export_as_runtime_bug_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the broken export alias syntax in the fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/export_as_runtime_bug_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the active wrapper export used until alias syntax works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
