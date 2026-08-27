# Bitfield Reorder Specification

> Tests covering Bitfield field reorder — attribute parsing, Bitfield field reorder — backend logic, Bitfield field reorder — HIR lowering, Bitfield field reorder — layoutattr factory defaults.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Reorder Specification

## Scenarios

### Bitfield field reorder — attribute parsing

#### LayoutAttr has is_preserve_order and is_compactq fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- LayoutAttr has is_preserve_order and is_compactq fields
   - Expected: src contains `is_preserve_order: bool`
   - Expected: src contains `is_compactq: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LayoutAttr has is_preserve_order and is_compactq fields")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("is_preserve_order: bool")).to_equal(true)
expect(src.contains("is_compactq: bool")).to_equal(true)
```

</details>

#### parse_layout_attrs recognises @preserve_order

- parse_layout_attrs recognises @preserve_order
   - Expected: src contains `attr.name == "preserve_order"`
   - Expected: src contains `is_preserve_order = true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_layout_attrs recognises @preserve_order")
val src = read_text("src/compiler/00.common/_Attributes/layout_attrs.spl")
expect(src.contains("attr.name == \"preserve_order\"")).to_equal(true)
expect(src.contains("is_preserve_order = true")).to_equal(true)
```

</details>

#### parse_layout_attrs recognises @compactq

- parse_layout_attrs recognises @compactq
   - Expected: src contains `attr.name == "compactq"`
   - Expected: src contains `is_compactq = true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_layout_attrs recognises @compactq")
val src = read_text("src/compiler/00.common/_Attributes/layout_attrs.spl")
expect(src.contains("attr.name == \"compactq\"")).to_equal(true)
expect(src.contains("is_compactq = true")).to_equal(true)
```

</details>

#### @repr(C) implies preserve_order in attribute parser

- @repr(C) implies preserve_order in attribute parser
   - Expected: src contains `layout_kind = TypeLayoutKind.C`
   - Expected: src contains `is_preserve_order = true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("@repr(C) implies preserve_order in attribute parser")
val src = read_text("src/compiler/00.common/_Attributes/layout_attrs.spl")
expect(src.contains("layout_kind = TypeLayoutKind.C")).to_equal(true)
expect(src.contains("is_preserve_order = true")).to_equal(true)
```

</details>

#### @repr(C) factory sets preserve_order true

- @repr(C) factory sets preserve_order true
   - Expected: src contains `layout_kind: TypeLayoutKind.C`
   - Expected: src contains `is_preserve_order: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("@repr(C) factory sets preserve_order true")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("layout_kind: TypeLayoutKind.C")).to_equal(true)
expect(src.contains("is_preserve_order: true")).to_equal(true)
```

</details>

### Bitfield field reorder — backend logic

#### defines sort_fields_by_width_desc function

- defines sort_fields_by_width_desc function
   - Expected: src contains `fn sort_fields_by_width_desc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines sort_fields_by_width_desc function")
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("fn sort_fields_by_width_desc")).to_equal(true)
```

</details>

#### defines would_straddle_word function

- defines would_straddle_word function
   - Expected: src contains `fn would_straddle_word`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines would_straddle_word function")
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("fn would_straddle_word")).to_equal(true)
```

</details>

#### compile_bitfield accepts preserve_order and compactq params

- compile_bitfield accepts preserve_order and compactq params
   - Expected: src contains `preserve_order: bool`
   - Expected: src contains `compactq: bool`
   - Expected: src contains `target_word_bits: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_bitfield accepts preserve_order and compactq params")
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("preserve_order: bool")).to_equal(true)
expect(src.contains("compactq: bool")).to_equal(true)
expect(src.contains("target_word_bits: i64")).to_equal(true)
```

</details>

#### compile_bitfield calls sort when not preserve_order

- compile_bitfield calls sort when not preserve_order
   - Expected: src contains `if not preserve_order`
   - Expected: src contains `sort_fields_by_width_desc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_bitfield calls sort when not preserve_order")
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("if not preserve_order")).to_equal(true)
expect(src.contains("sort_fields_by_width_desc")).to_equal(true)
```

</details>

#### compile_bitfield checks word straddle when not compactq

- compile_bitfield checks word straddle when not compactq
   - Expected: src contains `if not compactq`
   - Expected: src contains `would_straddle_word`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_bitfield checks word straddle when not compactq")
val src = read_text("src/compiler/70.backend/bitfield.spl")
expect(src.contains("if not compactq")).to_equal(true)
expect(src.contains("would_straddle_word")).to_equal(true)
```

</details>

### Bitfield field reorder — HIR lowering

#### lower_bitfield parses layout attrs from bitfield attributes

- lower_bitfield parses layout attrs from bitfield attributes
   - Expected: src contains `parse_layout_attrs(bitfield_attributes)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower_bitfield parses layout attrs from bitfield attributes")
val src = read_text("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
expect(src.contains("parse_layout_attrs(bitfield_attributes)")).to_equal(true)
```

</details>

#### lower_bitfield sorts fields by width descending

- lower_bitfield sorts fields by width descending
   - Expected: src contains `widths[indices[j - 1]] < widths[indices[j]]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower_bitfield sorts fields by width descending")
val src = read_text("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
expect(src.contains("widths[indices[j - 1]] < widths[indices[j]]")).to_equal(true)
```

</details>

#### lower_bitfield respects is_preserve_order

- lower_bitfield respects is_preserve_order
   - Expected: src contains `not layout_attr.is_preserve_order`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower_bitfield respects is_preserve_order")
val src = read_text("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
expect(src.contains("not layout_attr.is_preserve_order")).to_equal(true)
```

</details>

#### lower_bitfield avoids word straddle unless compactq

- lower_bitfield avoids word straddle unless compactq
   - Expected: src contains `not layout_attr.is_compactq`
   - Expected: src contains `word_end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower_bitfield avoids word straddle unless compactq")
val src = read_text("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
expect(src.contains("not layout_attr.is_compactq")).to_equal(true)
expect(src.contains("word_end")).to_equal(true)
```

</details>

### Bitfield field reorder — layoutattr factory defaults

#### layoutattr_default_ has preserve_order false

- layoutattr_default_ has preserve_order false
   - Expected: src contains `is_preserve_order: false`
   - Expected: src contains `is_compactq: false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("layoutattr_default_ has preserve_order false")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("is_preserve_order: false")).to_equal(true)
expect(src.contains("is_compactq: false")).to_equal(true)
```

</details>

#### layoutattr_c_repr has preserve_order true

- layoutattr_c_repr has preserve_order true
   - Expected: src contains `is_preserve_order: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("layoutattr_c_repr has preserve_order true")
val src = read_text("src/compiler/30.types/_TypeLayout/layout_core.spl")
expect(src.contains("is_preserve_order: true")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/bitfield_reorder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bitfield field reorder — attribute parsing, Bitfield field reorder — backend logic, Bitfield field reorder — HIR lowering, Bitfield field reorder — layoutattr factory defaults.
- Bitfield field reorder — attribute parsing
- Bitfield field reorder — backend logic
- Bitfield field reorder — HIR lowering
- Bitfield field reorder — layoutattr factory defaults

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `a221d37adb64ef5be0a76bbdd5367b2914a1cd0fa25cd604d3215aeaecae6996`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a221d37adb64ef5be0a76bbdd5367b2914a1cd0fa25cd604d3215aeaecae6996`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a221d37adb64ef5be0a76bbdd5367b2914a1cd0fa25cd604d3215aeaecae6996`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/bitfield_reorder_spec.spl
mirror: doc/06_spec/03_system/compiler/bitfield_reorder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/bitfield_reorder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/bitfield_reorder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/bitfield_reorder_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LayoutAttr has is_preserve_order and is_compactq fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/bitfield_reorder_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_layout_attrs recognises @preserve_order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/bitfield_reorder_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_layout_attrs recognises @compactq' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
