# SMF note.sdn Instantiation Tracking

> Tests the note.sdn section in SMF (Simple Module Format) for tracking generic instantiation metadata. The feature enables tracking which generic types and functions have been instantiated during compilation.

<!-- sdn-diagram:id=note_sdn_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=note_sdn_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

note_sdn_feature_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=note_sdn_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF note.sdn Instantiation Tracking

Tests the note.sdn section in SMF (Simple Module Format) for tracking generic instantiation metadata. The feature enables tracking which generic types and functions have been instantiated during compilation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GENERIC-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/usage/note_sdn_feature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the note.sdn section in SMF (Simple Module Format) for tracking generic
instantiation metadata. The feature enables tracking which generic
types and functions have been instantiated during compilation.

## Syntax

```simple
# note.sdn records generic instantiations
# e.g., List<Int> instantiated at line 42
```

## Scenarios

### SMF note.sdn Instantiation Tracking

#### tracks generic instantiation metadata

1. var ctx = JitCompilationContext from smf
2. ctx record instantiation
   - Expected: ctx.recorded.len() equals `1`
   - Expected: ctx.recorded[0].template_name equals `List`
   - Expected: ctx.recorded[0].mangled_name equals `List$Int`
   - Expected: ctx.recorded[0].success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = JitCompilationContext.from_smf({})
ctx.record_instantiation("List", [make_named_type("Int")], "List$Int", true, nil)

expect(ctx.recorded.len()).to_equal(1)
expect(ctx.recorded[0].template_name).to_equal("List")
expect(ctx.recorded[0].mangled_name).to_equal("List$Int")
expect(ctx.recorded[0].success).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
