# Bitfield Feature Plan

> Tests the bitfield feature plan by verifying parser phase scope, validation phase scope, and coverage path tracking. Ensures the bitfield declaration syntax, storage widths, field widths, and reserved field support are properly scoped and linked to the canonical implementation plan.

<!-- sdn-diagram:id=bitfield_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitfield_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitfield_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitfield_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Feature Plan

Tests the bitfield feature plan by verifying parser phase scope, validation phase scope, and coverage path tracking. Ensures the bitfield declaration syntax, storage widths, field widths, and reserved field support are properly scoped and linked to the canonical implementation plan.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/bitfield_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the bitfield feature plan by verifying parser phase scope, validation phase scope,
and coverage path tracking. Ensures the bitfield declaration syntax, storage widths,
field widths, and reserved field support are properly scoped and linked to the
canonical implementation plan.

## Scenarios

### Bitfield Feature Plan

#### locks parser phase scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(PARSER_PHASE)).to_equal(3)
expect(has_text(PARSER_PHASE, "keyword: bitfield")).to_equal(true)
expect(has_text(PARSER_PHASE, "declaration syntax: bitfield Name(BackingType):")).to_equal(true)
```

</details>

#### locks validation phase scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(VALIDATION_PHASE)).to_equal(3)
expect(has_text(VALIDATION_PHASE, "storage widths: u8/u16/u32/u64")).to_equal(true)
expect(has_text(VALIDATION_PHASE, "reserved fields: _")).to_equal(true)
```

</details>

#### links to canonical implementation plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = ["doc/03_plan/bitfield_feature_plan_2026-02-24.md"]
expect(count_texts(docs)).to_equal(1)
expect(has_text(docs, "doc/03_plan/bitfield_feature_plan_2026-02-24.md")).to_equal(true)
```

</details>

#### tracks executable coverage paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_texts(COVERAGE_PATHS)).to_equal(6)
expect(has_text(COVERAGE_PATHS, "test/feature/usage/bitfield_runtime_compat_spec.spl")).to_equal(true)
expect(has_text(COVERAGE_PATHS, "test/unit/compiler/parser/bitfield_pure_simple_spec.spl")).to_equal(true)
expect(has_text(COVERAGE_PATHS, "test/unit/compiler/native/bitfield_codegen_spec.spl")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
