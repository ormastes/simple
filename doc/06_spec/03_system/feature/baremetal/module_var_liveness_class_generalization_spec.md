# Module Var Liveness Class Generalization Specification

> Tests covering module-level var liveness as seen from an it body.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Var Liveness Class Generalization Specification

## Scenarios

### module-level var liveness as seen from an it body

#### i64: a two-hop helper write is visible to a direct read

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- i64: a two-hop helper write is visible to a direct read
   - Expected: gi equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("i64: a two-hop helper write is visible to a direct read")
set_i_indirect(21)
expect(gi).to_equal(21)
```

</details>

#### i64: compound assignment through a helper is visible to a direct read

- i64: compound assignment through a helper is visible to a direct read
   - Expected: gi equals `105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("i64: compound assignment through a helper is visible to a direct read")
set_i(100)
bump_i(5)
expect(gi).to_equal(105)
```

</details>

#### i64: a second write during the same body is seen by a second read

- i64: a second write during the same body is seen by a second read
   - Expected: gi equals `1`
   - Expected: gi equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("i64: a second write during the same body is seen by a second read")
set_i(1)
expect(gi).to_equal(1)
set_i(2)
expect(gi).to_equal(2)
```

</details>

#### text: a helper write is visible to a direct read

- text: a helper write is visible to a direct read
   - Expected: gs equals `live`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("text: a helper write is visible to a direct read")
set_s("live")
expect(gs).to_equal("live")
```

</details>

#### bool: a helper write is visible to a direct read

- bool: a helper write is visible to a direct read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bool: a helper write is visible to a direct read")
set_b(true)
assert_true(gb)
```

</details>

#### array: a helper write is visible to a direct read

- array: a helper write is visible to a direct read
   - Expected: ga.len() equals `2`
   - Expected: ga[0] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array: a helper write is visible to a direct read")
set_a(7)
expect(ga.len()).to_equal(2)
expect(ga[0]).to_equal(7)
```

</details>

#### a same-named local still shadows the module var

- a same-named local still shadows the module var
   - Expected: gi equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a same-named local still shadows the module var")
set_i(500)
val gi = 3
expect(gi).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module-level var liveness as seen from an it body.
- module-level var liveness as seen from an it body

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6826e2f325aa3a3ae4b0b082162617a156b1089c94755fb254678535ce2b48a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6826e2f325aa3a3ae4b0b082162617a156b1089c94755fb254678535ce2b48a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6826e2f325aa3a3ae4b0b082162617a156b1089c94755fb254678535ce2b48a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i64: a two-hop helper write is visible to a direct read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i64: compound assignment through a helper is visible to a direct read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/module_var_liveness_class_generalization_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i64: a second write during the same body is seen by a second read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
