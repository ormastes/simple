# Frontend Registry Transient Owner Specification

> Tests covering frontend registry transient ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Frontend Registry Transient Owner Specification

## Scenarios

### frontend registry transient ownership

#### retains prior module claims across a reclaimed parse scope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains prior module claims across a reclaimed parse scope
   - Expected: aspect_registry_claim_keys().len() equals `2`
   - Expected: effect_registry_claim_keys().len() equals `2`
   - Expected: layer_eq_registry_claim_keys().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains prior module claims across a reclaimed parse scope")
aspect_registry_reset()
effect_registry_reset()
layer_eq_registry_reset()

expect(rt_transient_array_scope_begin()).to_be(true)
record_registry_claims("first.module")
expect(rt_transient_array_scope_pause()).to_be(true)
expect(promote_registry_owners()).to_be(true)
expect(rt_transient_array_scope_end()).to_be(true)

expect(rt_transient_array_scope_begin()).to_be(true)
record_registry_claims("second.module")
expect(rt_transient_array_scope_pause()).to_be(true)
expect(promote_registry_owners()).to_be(true)
expect(rt_transient_array_scope_end()).to_be(true)

expect(aspect_registry_claim_keys().len()).to_equal(2)
expect(effect_registry_claim_keys().len()).to_equal(2)
expect(layer_eq_registry_claim_keys().len()).to_equal(2)
```

</details>

#### removes only the reparsed module from every registry

- removes only the reparsed module from every registry
   - Expected: aspect_registry_claim_keys().len() equals `1`
   - Expected: effect_registry_claim_keys().len() equals `1`
   - Expected: layer_eq_registry_claim_keys().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("removes only the reparsed module from every registry")
expect(rt_transient_array_scope_begin()).to_be(true)
aspect_registry_reset_module("first.module")
effect_registry_reset_module("first.module")
layer_eq_registry_reset_module("first.module")
expect(rt_transient_array_scope_pause()).to_be(true)
expect(promote_registry_owners()).to_be(true)
expect(rt_transient_array_scope_end()).to_be(true)

expect(aspect_registry_claim_keys().len()).to_equal(1)
expect(effect_registry_claim_keys().len()).to_equal(1)
expect(layer_eq_registry_claim_keys().len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering frontend registry transient ownership.
- frontend registry transient ownership

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8146c38476fd9d099fb0e6cfed7fae49e51b56289941501a6495bfa3195634dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8146c38476fd9d099fb0e6cfed7fae49e51b56289941501a6495bfa3195634dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8146c38476fd9d099fb0e6cfed7fae49e51b56289941501a6495bfa3195634dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains prior module claims across a reclaimed parse scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/frontend_registry_transient_owner_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes only the reparsed module from every registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
