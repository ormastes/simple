# Monomorphization Native Build Regression Specification

> <details>

<!-- sdn-diagram:id=monomorphization_native_build_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=monomorphization_native_build_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

monomorphization_native_build_regression_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=monomorphization_native_build_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Monomorphization Native Build Regression Specification

## Scenarios

### monomorphization native-build regression

#### scans block and field expressions without rt_enum_discriminant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = module_with_generic_function()
val (output, stats) = run_monomorphization({"mono.regression": input})

expect(output.len()).to_equal(1)
expect(stats.generic_functions_found).to_equal(1)
expect(stats.call_sites_found).to_equal(1)
```

</details>

#### keeps direct mono compiles off root std.sdn and relative HIR imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_source = rt_file_read_text("src/compiler/40.mono/monomorphize/cache.spl") ?? ""
val hot_reload_source = rt_file_read_text("src/compiler/40.mono/monomorphize/hot_reload.spl") ?? ""
val engine_source = rt_file_read_text("src/compiler/40.mono/monomorphize/engine.spl") ?? ""

expect(cache_source.contains("use std.sdn.")).to_equal(false)
expect(hot_reload_source.contains("use std.sdn.")).to_equal(false)
expect(engine_source.contains("use hir_types.*")).to_equal(false)
expect(engine_source.contains("use hir_definitions.*")).to_equal(false)
expect(cache_source).to_contain("use std.common.sdn.parser (parse)")
expect(engine_source).to_contain("use compiler.hir.hir_types.*")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- monomorphization native-build regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
