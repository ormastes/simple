# Group Import Shadowing Generalization Specification

> Tests covering group import shadowing generalization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Group Import Shadowing Generalization Specification

## Scenarios

### group import shadowing generalization

#### nested self-named module binds the class member

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- nested self-named module binds the class member
   - Expected: Gadget.kind() equals `gadget`
   - Expected: g.id equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested self-named module binds the class member")
expect(Gadget.kind()).to_equal("gadget")
val g = Gadget(id: 3)
expect(g.id).to_equal(3)
```

</details>

#### sibling function imported alongside the self-named class works

- sibling function imported alongside the self-named class works
   - Expected: gadget_default() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sibling function imported alongside the self-named class works")
expect(gadget_default()).to_equal(11)
```

</details>

#### aliased import binds the class under the alias

- aliased import binds the class under the alias
   - Expected: w.size equals `5`
   - Expected: W.kind() equals `widget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aliased import binds the class under the alias")
val w = W(size: 5)
expect(w.size).to_equal(5)
expect(W.kind()).to_equal("widget")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering group import shadowing generalization.
- group import shadowing generalization

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `20d5d9694ccacd414497223510e5401b12d340c52fdcd03b834f1a74f661eaee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20d5d9694ccacd414497223510e5401b12d340c52fdcd03b834f1a74f661eaee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20d5d9694ccacd414497223510e5401b12d340c52fdcd03b834f1a74f661eaee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl
mirror: doc/06_spec/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nested self-named module binds the class member' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sibling function imported alongside the self-named class works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aliased import binds the class under the alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
