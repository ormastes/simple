# Macro Import Theorem1 Minimal Specification

> 1. expect exports is well formed

<!-- sdn-diagram:id=macro_import_theorem1_minimal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_import_theorem1_minimal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_import_theorem1_minimal_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_import_theorem1_minimal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Import Theorem1 Minimal Specification

## Scenarios

### Lean Theorem 1: glob_doesnt_leak_macros_wf

#### macro not in auto-import is excluded from glob

1. expect exports is well formed
2. var manifest = MacroDirManifest new
3. manifest add auto import


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
expect exports.is_well_formed()

var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val result = glob_import(manifest, exports)

# other_macro should NOT be in result
var found_other = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "other_macro":
        found_other = true

expect not found_other

# my_macro SHOULD be in result
var found_my = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "my_macro":
        found_my = true

expect found_my
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/dependency/macro_import_theorem1_minimal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Theorem 1: glob_doesnt_leak_macros_wf

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
