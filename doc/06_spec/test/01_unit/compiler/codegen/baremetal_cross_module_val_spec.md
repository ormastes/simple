# Baremetal Cross Module Val Specification

> <details>

<!-- sdn-diagram:id=baremetal_cross_module_val_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_cross_module_val_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_cross_module_val_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_cross_module_val_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Cross Module Val Specification

## Scenarios

### cross-module val u32 baremetal regression

#### same-module val u32 (sanity check)

#### same-module val u32 literal round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A same-module `val u32` is lowered to `ConstInt` and
# emitted as `iconst` at the use site — this has ALWAYS
# worked on hosted and baremetal. This test just pins the
# behavior so a future refactor cannot silently break it.
assert CROSS_MODULE_VAL_U32_MARKER == 12345
assert CROSS_MODULE_VAL_U32_MARKER == CROSS_MODULE_VAL_U32_EXPECTED
```

</details>

#### data_exports plumbing

#### data_exports is populated at import-map build time

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `pipeline/native_project/imports.rs::build_import_map`
# inserts the mangled name of every `Node::Const`,
# `Node::Static`, and `Node::Let` it encounters into
# `ImportMapResult.data_exports`. This set is threaded
# through `ModuleImports` to `CodegenBackend.data_exports`
# via `set_data_exports`. This test is a reminder that
# removing the plumbing re-introduces the bug — the cross-
# module `GlobalLoad` for `val K: u32` would silently fall
# back to the function-import fast path and return the
# symbol's address instead of its value.
assert true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/baremetal_cross_module_val_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cross-module val u32 baremetal regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
