# Driver Memory Lifecycle Family Specification

> Tests covering driver memory lifecycle family invariants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Memory Lifecycle Family Specification

## Scenarios

### driver memory lifecycle family invariants

#### keeps the three phase evictions reference-drop only

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the three phase evictions reference-drop only
   - Expected: source does not contain `rt_dict_free_deep(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the three phase evictions reference-drop only")
val source = file_read(TYPES)
expect(source).to_contain("me evict_ast():")
expect(source).to_contain("me evict_hir():")
# No deep-free CALL anywhere in the driver context (the name appears once
# more, in the prohibition comment asserted by the next example).
expect(source.contains("rt_dict_free_deep(")).to_equal(false)
```

</details>

#### retains the measured rationale that forbids a deep free

- retains the measured rationale that forbids a deep free


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains the measured rationale that forbids a deep free")
val source = file_read(TYPES)
expect(source).to_contain("Do NOT \"fix\" this by calling rt_dict_free_deep here")
expect(source).to_contain("reclaims NOTHING")
```

</details>

#### records that the real fix is a codegen change, not a driver change

- records that the real fix is a codegen change, not a driver change


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records that the real fix is a codegen change, not a driver change")
val source = file_read(TYPES)
expect(source).to_contain("NOT a driver change")
```

</details>

<details>
<summary>Advanced: never constructs the HIR lowerer inside the per-source loop</summary>

#### never constructs the HIR lowerer inside the per-source loop

- never constructs the HIR lowerer inside the per-source loop
   - Expected: body does not contain `hirlowering_for_module_with_diagnostics(`
   - Expected: body does not contain `hirlowering_new()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never constructs the HIR lowerer inside the per-source loop")
val source = file_read(HIR)
val loop = source.index_of("while source_idx < self.ctx.sources.len():")
expect(loop).to_be_greater_than(0)
val body = source.substring(loop, source.len())
expect(body.contains("hirlowering_for_module_with_diagnostics(")).to_equal(false)
expect(body.contains("hirlowering_new()")).to_equal(false)
```

</details>


</details>

#### reuses one diagnostics buffer and one trait-registry owner

- reuses one diagnostics buffer and one trait-registry owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reuses one diagnostics buffer and one trait-registry owner")
val source = file_read(HIR)
expect(source).to_contain("Allocate the diagnostics array before the long HIR loop")
expect(source).to_contain("This loop-owned lowerer is the trait registry owner")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver memory lifecycle family invariants.
- driver memory lifecycle family invariants

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
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08ff9fad0850f8baee914a40e0db93e026ad5e23460cc3ff6cd2f257ad8a2f2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08ff9fad0850f8baee914a40e0db93e026ad5e23460cc3ff6cd2f257ad8a2f2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08ff9fad0850f8baee914a40e0db93e026ad5e23460cc3ff6cd2f257ad8a2f2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the three phase evictions reference-drop only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the measured rationale that forbids a deep free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records that the real fix is a codegen change, not a driver change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
