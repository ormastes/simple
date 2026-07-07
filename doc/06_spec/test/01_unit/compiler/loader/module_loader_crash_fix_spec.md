# Module Loader Crash Fix Specification

> <details>

<!-- sdn-diagram:id=module_loader_crash_fix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_crash_fix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_crash_fix_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_crash_fix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Crash Fix Specification

## Scenarios

### Module Loader Crash Fix

#### exposes safe method-based constructor functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ModuleLoaderConfig.default()
val loader = ModuleLoader.new(config)

expect(config.enable_jit).to_equal(true)
expect(loader.config.max_cache_size).to_equal(100)
```

</details>

#### supports reload without recursive unload failures

- var loader = ModuleLoader with defaults
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val missing = moduleloader_reload(loader, "test/unit/compiler/loader/missing_for_reload.spl")

match missing:
    case LoadResult.Error(message):
        expect(message).to_contain("module not found")
    case _:
        fail("expected reload error for missing path")
```

</details>

#### allows unloading an unknown path safely

- var loader = ModuleLoader with defaults
- moduleloader unload
   - Expected: loader.stats().module_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
moduleloader_unload(loader, "test/unit/compiler/loader/unknown_path.spl")
expect(loader.stats().module_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/module_loader_crash_fix_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module Loader Crash Fix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
