# Spec To Sspec Merge Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec To Sspec Merge Specification

## Scenarios

### spec-to-SSpec preservation

#### preserves manual tests when adding generated coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manual = "describe \"manual\":\n    it \"keeps behavior\":\n        expect(1).to_equal(1)"
val generated = "# spec-to-sspec:generated:start\n# @feature: css.display\n# spec-to-sspec:generated:end"
val merged = merge_generated_spec(manual, generated)
expect(merged).to_contain("keeps behavior")
expect(merged).to_contain("@feature: css.display")
```

</details>

#### updates only the previously generated region

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val existing = "manual-before\n# spec-to-sspec:generated:start\nold-generated\n# spec-to-sspec:generated:end\nmanual-after"
val generated = "# spec-to-sspec:generated:start\nnew-generated\n# spec-to-sspec:generated:end"
val merged = merge_generated_spec(existing, generated)
expect(merged).to_contain("manual-before")
expect(merged).to_contain("new-generated")
expect(merged).to_contain("manual-after")
expect(merged.contains("old-generated")).to_equal(false)
```

</details>

#### keeps unsupported examples visibly pending instead of false green

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generated = "# spec-to-sspec:generated:start\npending(\"Specification has no executable examples\")\n# spec-to-sspec:generated:end"
val merged = merge_generated_spec("", generated)
expect(merged).to_contain("pending(")
expect(merged.contains("expect(true)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/spec_to_sspec_merge_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spec-to-SSpec preservation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
