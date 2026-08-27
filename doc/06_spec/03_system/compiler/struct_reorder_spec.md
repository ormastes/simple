# Struct Reorder Specification

> Tests covering Struct field reorder — Simple layout functions, Struct field reorder — layout dispatch, Struct field reorder — Rust seed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Reorder Specification

## Scenarios

### Struct field reorder — Simple layout functions

#### defines reorder_fields_by_size function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines reorder_fields_by_size function
   - Expected: src contains `fn reorder_fields_by_size(fields: [HirField]) -> [HirField]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines reorder_fields_by_size function")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("fn reorder_fields_by_size(fields: [HirField]) -> [HirField]")).to_equal(true)
```

</details>

#### defines arch-aware reorder_fields_by_size_for_arch

- defines arch-aware reorder_fields_by_size_for_arch
   - Expected: src contains `fn reorder_fields_by_size_for_arch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines arch-aware reorder_fields_by_size_for_arch")
val src = read_text("src/compiler/30.types/_TypeLayout/arch_and_verify.spl")
expect(src.contains("fn reorder_fields_by_size_for_arch")).to_equal(true)
```

</details>

#### sorts by size descending using insertion sort

- sorts by size descending using insertion sort
   - Expected: src contains `sizes[indices[j - 1]] < sizes[indices[j]]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sorts by size descending using insertion sort")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("sizes[indices[j - 1]] < sizes[indices[j]]")).to_equal(true)
```

</details>

### Struct field reorder — layout dispatch

#### Simple layout reorders fields when not preserve_order

- Simple layout reorders fields when not preserve_order
   - Expected: src contains `reorder_fields_by_size(fields)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Simple layout reorders fields when not preserve_order")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("reorder_fields_by_size(fields)")).to_equal(true)
```

</details>

#### Simple layout skips reorder when preserve_order

- Simple layout skips reorder when preserve_order
   - Expected: src contains `attr.is_preserve_order`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Simple layout skips reorder when preserve_order")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("attr.is_preserve_order")).to_equal(true)
```

</details>

#### compactq uses packed layout with reordered fields

- compactq uses packed layout with reordered fields
   - Expected: src contains `attr.is_compactq`
   - Expected: src contains `compute_packed_layout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compactq uses packed layout with reordered fields")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("attr.is_compactq")).to_equal(true)
expect(src.contains("compute_packed_layout")).to_equal(true)
```

</details>

#### C layout always preserves field order

- C layout always preserves field order
   - Expected: src contains `case TypeLayoutKind.C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("C layout always preserves field order")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("case TypeLayoutKind.C")).to_equal(true)
```

</details>

### Struct field reorder — Rust seed

#### StructLayout has new_with_options method

- StructLayout has new_with_options method
   - Expected: src contains `pub fn new_with_options`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("StructLayout has new_with_options method")
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("pub fn new_with_options")).to_equal(true)
```

</details>

#### new_with_options accepts preserve_order and compactq

- new_with_options accepts preserve_order and compactq
   - Expected: src contains `preserve_order: bool`
   - Expected: src contains `compactq: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("new_with_options accepts preserve_order and compactq")
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("preserve_order: bool")).to_equal(true)
expect(src.contains("compactq: bool")).to_equal(true)
```

</details>

#### Rust seed sorts fields by size descending

- Rust seed sorts fields by size descending
   - Expected: src contains `b.1.cmp(&a.1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Rust seed sorts fields by size descending")
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("b.1.cmp(&a.1)")).to_equal(true)
```

</details>

#### Rust seed uses alignment 1 for compactq

- Rust seed uses alignment 1 for compactq
   - Expected: src contains `effective_align = if compactq`
   - Expected: src contains `effective_max = if compactq`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Rust seed uses alignment 1 for compactq")
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("effective_align = if compactq")).to_equal(true)
expect(src.contains("effective_max = if compactq")).to_equal(true)
```

</details>

#### new delegates to new_with_options with defaults

- new delegates to new_with_options with defaults
   - Expected: src contains `Self::new_with_options(name, fields, registry, has_vtable, type_id, false, fa... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("new delegates to new_with_options with defaults")
val src = read_text("src/compiler_rust/compiler/src/hir/types/layout.rs")
expect(src.contains("Self::new_with_options(name, fields, registry, has_vtable, type_id, false, false)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/struct_reorder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Struct field reorder — Simple layout functions, Struct field reorder — layout dispatch, Struct field reorder — Rust seed.
- Struct field reorder — Simple layout functions
- Struct field reorder — layout dispatch
- Struct field reorder — Rust seed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `045f1c37eced3f31b495802aca5d04eb531ac9d52d2155503fe1ab735d8f5e4c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `045f1c37eced3f31b495802aca5d04eb531ac9d52d2155503fe1ab735d8f5e4c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `045f1c37eced3f31b495802aca5d04eb531ac9d52d2155503fe1ab735d8f5e4c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/struct_reorder_spec.spl
mirror: doc/06_spec/03_system/compiler/struct_reorder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/struct_reorder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/struct_reorder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/struct_reorder_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines reorder_fields_by_size function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/struct_reorder_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines arch-aware reorder_fields_by_size_for_arch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/struct_reorder_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts by size descending using insertion sort' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
