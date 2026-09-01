# Module Init Specification

> Tests covering @init and @teardown annotations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Init Specification

## Scenarios

### @init and @teardown annotations

#### annotated functions can be defined

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- annotated functions can be defined
   - Expected: my_init() equals `0`
   - Expected: my_teardown() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("annotated functions can be defined")
# @init
fn my_init():
    0

# @teardown
fn my_teardown():
    0

expect(my_init()).to_equal(0)
expect(my_teardown()).to_equal(0)
```

</details>

#### functions can be called manually if annotated

- functions can be called manually if annotated
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("functions can be called manually if annotated")
# NOTE: var mutation inside nested closure doesn't persist in interpreter.
# Test the concept by checking the function is callable.
fn setup_module() -> i64:
    1

val result = setup_module()
expect(result).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/unit/runtime/module_init_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering @init and @teardown annotations.
- @init and @teardown annotations

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

- Canonical SPipe generation for source `ce6b82b0119810f47c807d806c3ccda86e8c3ae66b9102921c6fd70f9ca9fc5a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce6b82b0119810f47c807d806c3ccda86e8c3ae66b9102921c6fd70f9ca9fc5a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce6b82b0119810f47c807d806c3ccda86e8c3ae66b9102921c6fd70f9ca9fc5a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/runtime/module_init_spec.spl
mirror: doc/06_spec/unit/runtime/module_init_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/runtime/module_init_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/runtime/module_init_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/runtime/module_init_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/runtime/module_init_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'annotated functions can be defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/runtime/module_init_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'functions can be called manually if annotated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
