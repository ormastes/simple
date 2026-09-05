# Payload Binding Contest Names Agree Source Specification

> Tests covering materialized payload binding contest requires name agreement.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Payload Binding Contest Names Agree Source Specification

## Scenarios

### materialized payload binding contest requires name agreement

#### declares a positive name-agreement predicate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares a positive name-agreement predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares a positive name-agreement predicate")
val modules = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
expect(modules).to_contain("fn hir_payload_binding_names_agree(local_name: text, origin_item_name: text, symbol_name: text) -> bool")
expect(modules).to_contain("symbol_name == local_name or symbol_name == origin_item_name")
```

</details>

#### gates the non-type contest on name agreement

- gates the non-type contest on name agreement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates the non-type contest on name agreement")
val modules = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
expect(modules).to_contain("val contestable = hir_payload_binding_names_agree(local_name, origin.item_name, symbol.name)")
expect(modules).to_contain("if contestable and not hir_payload_kind_is_type(existing_kind):")
expect(modules).to_not_contain("if not hir_payload_kind_is_type(existing_kind):")
```

</details>

#### gates the identity conflict on name agreement too

- gates the identity conflict on name agreement too


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates the identity conflict on name agreement too")
# A name mismatch invalidates the identity comparison exactly as much
# as it invalidates the kind comparison, so this contest is gated too.
val modules = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
expect(modules).to_contain("if contestable and existing != wanted:")
```

</details>

#### keeps the positive kind predicate rather than an emptiness test

- keeps the positive kind predicate rather than an emptiness test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the positive kind predicate rather than an emptiness test")
# Regression fence for 513cbb7b4: the old emptiness test never fired,
# because callables and constants map to non-empty kinds.
val modules = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
expect(modules).to_contain("fn hir_payload_kind_is_type(kind: text) -> bool")
```

</details>

#### keeps the re-entrancy breaker as a list, not a Dict

- keeps the re-entrancy breaker as a list, not a Dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the re-entrancy breaker as a list, not a Dict")
# The breaker is a separate defect (stack exhaustion). Every breaker in
# this cycle that memoized on Dict membership has failed open once.
val modules = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
val types = rt_file_read_text("src/compiler/20.hir/hir_lowering/types.spl") ?? ""
expect(modules).to_contain("if self.imported_type_methods_in_progress_has(reentry_key):")
expect(modules).to_contain("self.register_imported_type_methods_inner(")
expect(types).to_contain("imported_type_methods_in_progress: [text]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering materialized payload binding contest requires name agreement.
- materialized payload binding contest requires name agreement

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

- Canonical SPipe generation for source `db00f3400a8ae4aa8cda24951f9b1eb59ebd2f17b6ef9245cc78b465501312dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db00f3400a8ae4aa8cda24951f9b1eb59ebd2f17b6ef9245cc78b465501312dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db00f3400a8ae4aa8cda24951f9b1eb59ebd2f17b6ef9245cc78b465501312dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares a positive name-agreement predicate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates the non-type contest on name agreement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates the identity conflict on name agreement too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
