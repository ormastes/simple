# Macro Import Theorem1 Specification

> 1. var manifest = MacroDirManifest new

<!-- sdn-diagram:id=macro_import_theorem1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_import_theorem1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_import_theorem1_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_import_theorem1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Import Theorem1 Specification

## Scenarios

### Lean Theorem 1: glob_doesnt_leak_macros_wf

#### macro not in auto-import is excluded

1. var manifest = MacroDirManifest new
2. manifest add auto import


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()

var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val result = glob_import(manifest, exports)

var found_other = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "other_macro":
        found_other = true

expect not found_other
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/dependency/macro_import_theorem1_spec.spl` |
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
