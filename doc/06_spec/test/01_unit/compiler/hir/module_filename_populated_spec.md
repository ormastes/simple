# Module Filename Populated Specification

> 1. var lowering = HirLowering with filename

<!-- sdn-diagram:id=module_filename_populated_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_filename_populated_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_filename_populated_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_filename_populated_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Filename Populated Specification

## Scenarios

### Symbol.defining_module populated from module_filename

#### single module: symbols carry the source path

1. var lowering = HirLowering with filename
   - Expected: all_match is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn greet() -> text:\n    \"hello\""
val path = "src/greet.spl"
val log = make_logger()
val module = parse_full_frontend(src, path, "greet", log)
var lowering = HirLowering.with_filename(path)
val hir = lowering.lower_module(module)

# Every symbol defined in the HIR must reference the source path
var all_match = true
for sym in hir.symbols.symbols.values():
    if sym.defining_module.?:
        if sym.defining_module.unwrap() != path:
            all_match = false
    else:
        all_match = false
expect(all_match).to_equal(true)
```

</details>

#### two modules: symbols carry distinct source paths

1. var lowering a = HirLowering with filename
2. var lowering b = HirLowering with filename
   - Expected: a_ok is true
   - Expected: b_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = make_logger()

val src_a = "fn alpha() -> i64:\n    1"
val path_a = "src/mod_a.spl"
val module_a = parse_full_frontend(src_a, path_a, "mod_a", log)
var lowering_a = HirLowering.with_filename(path_a)
val hir_a = lowering_a.lower_module(module_a)

val src_b = "fn beta() -> i64:\n    2"
val path_b = "src/mod_b.spl"
val module_b = parse_full_frontend(src_b, path_b, "mod_b", log)
var lowering_b = HirLowering.with_filename(path_b)
val hir_b = lowering_b.lower_module(module_b)

# All symbols in hir_a must reference path_a
var a_ok = true
for sym in hir_a.symbols.symbols.values():
    if sym.defining_module.?:
        if sym.defining_module.unwrap() != path_a:
            a_ok = false
    else:
        a_ok = false
expect(a_ok).to_equal(true)

# All symbols in hir_b must reference path_b
var b_ok = true
for sym in hir_b.symbols.symbols.values():
    if sym.defining_module.?:
        if sym.defining_module.unwrap() != path_b:
            b_ok = false
    else:
        b_ok = false
expect(b_ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_filename_populated_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Symbol.defining_module populated from module_filename

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
