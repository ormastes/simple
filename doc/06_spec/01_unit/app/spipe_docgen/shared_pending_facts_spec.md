# Shared Pending Facts Specification

> Tests covering Docgen shared lexical facts preserve pending ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Pending Facts Specification

## Scenarios

### Docgen shared lexical facts preserve pending ownership

#### counts active conditional gates separately from unconditional placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"gate\":\n    it \"active\":\n        if false:\n            pass_todo\n        expect(2).to_equal(2)\n    it \"pending\":\n        pass_todo\n"
val counts = count_test_items(source)
expect(counts.0).to_equal(1)
expect(counts.1).to_equal(0)
expect(counts.2).to_equal(1)
```

</details>

#### keeps column-zero fixture string lines inside their scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"fixture\":\n    it \"pending after fixture\":\n        val sample = \"\"\"\ncolumn zero\n\"\"\"\n        pass_todo\n"
val lines = source.split("\n")
val continuation = simple_string_continuation_lines(source)
expect(scenario_at_is_unconditional_pending_with_facts(lines, continuation, 1)).to_equal(true)
expect(scenario_at_is_unconditional_pending_with_facts(lines, continuation, -1)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_docgen/shared_pending_facts_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Docgen shared lexical facts preserve pending ownership.
- Docgen shared lexical facts preserve pending ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
