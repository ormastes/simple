# Gc Boundary Check Specification

> <details>

<!-- sdn-diagram:id=gc_boundary_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_boundary_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_boundary_check_spec -> std
gc_boundary_check_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_boundary_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Boundary Check Specification

## Scenarios

### gc boundary semantic checker

#### warns when no-gc imports gc async

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_gc_boundary_imports(
    "std.nogc_sync_mut.fs",
    ["std.gc_async_mut.gpu"]
)
expect(warnings.len()).to_equal(1)
expect(warnings[0].message).to_contain("no-gc module")
expect(warnings[0].message).to_contain("imports GC family")
```

</details>

#### warns when gc async imports no-gc (symmetric rule)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_gc_boundary_imports(
    "std.gc_async_mut.gpu",
    ["std.nogc_sync_mut.fs"]
)
expect(warnings.len()).to_equal(1)
expect(warnings[0].message).to_contain("gc module")
expect(warnings[0].message).to_contain("imports no-gc family")
```

</details>

#### warns when noalloc imports allocating no-gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_gc_boundary_imports(
    "std.nogc_async_mut_noalloc.memory",
    ["std.nogc_async_mut.actor"]
)
expect(warnings.len()).to_equal(1)
expect(warnings[0].message).to_contain("no-alloc module")
expect(warnings[0].message).to_contain("imports allocating family")
```

</details>

#### warns when noalloc imports gc async

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_gc_boundary_imports(
    "std.nogc_async_mut_noalloc.memory",
    ["std.gc_async_mut.gpu"]
)
expect(warnings.len()).to_equal(1)
expect(warnings[0].message).to_contain("imports GC family")
```

</details>

#### allows common imports from no-gc and noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_gc_boundary_imports(
    "std.nogc_async_mut_noalloc.memory",
    ["std.common.text"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### formats produced family warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_gc_boundary_imports(
    "std.nogc_async_mut.actor",
    ["std.gc_async_mut.gpu"]
)
val messages = format_family_warnings(warnings)
expect(messages.len()).to_equal(1)
expect(messages[0]).to_contain("gc_boundary_crossing")
```

</details>

#### classifies runtime families through the manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val noalloc = runtime_family_manifest_entry("std.nogc_async_mut_noalloc.memory")
expect(noalloc.family).to_equal("nogc_async_mut_noalloc")
expect(noalloc.noalloc).to_equal(true)
expect(noalloc.allocates).to_equal(false)

val gc = runtime_family_manifest_entry("std.gc_sync_immut.map")
expect(gc.gc_mode).to_equal("gc")
expect(gc.rank).to_equal(4)
```

</details>

#### returns hard violations from the manifest-backed model

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val violations = check_runtime_family_import_violations(
    "std.nogc_async_mut_noalloc.memory",
    ["std.nogc_async_mut.actor", "std.gc_async_mut.gpu", "std.common.text"]
)
expect(violations.len()).to_equal(2)
expect(violations[0].reason).to_equal("noalloc_imports_allocating_family")
expect(violations[1].reason).to_equal("noalloc_imports_gc_family")
```

</details>

#### rejects lower runtime layers importing hosted adapters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val violations = check_runtime_family_import_violations(
    "std.nogc_async_mut.actor",
    ["std.nogc_sync_mut.io"]
)
expect(violations.len()).to_equal(1)
expect(violations[0].reason).to_equal("higher_layer_runtime_family")
```

</details>

#### warns when nogc module imports std.gpu alias (gc-backed shim)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# std.gpu is exposed via nogc_async_mut/gpu/__init__.spl which does
# `use gc_async_mut.gpu.*` — the alias resolver must detect this.
val warnings = check_gc_boundary_imports(
    "std.nogc_sync_mut.fs",
    ["std.gpu"]
)
expect(warnings.len()).to_equal(1)
expect(warnings[0].message).to_contain("no-gc module")
expect(warnings[0].message).to_contain("imports GC family")
```

</details>

#### warns when nogc module imports std.nogc_async_mut.gpu (gc-backed shim)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# std.nogc_async_mut.gpu/__init__.spl re-exports gc_async_mut.gpu.*;
# the alias resolver classifies it as gc family despite the nogc_ prefix.
val warnings = check_gc_boundary_imports(
    "std.nogc_sync_mut.fs",
    ["std.nogc_async_mut.gpu"]
)
expect(warnings.len()).to_equal(1)
expect(warnings[0].message).to_contain("no-gc module")
expect(warnings[0].message).to_contain("imports GC family")
```

</details>

#### does not warn when gc module imports std.gpu alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A gc_async_mut module importing std.gpu (also gc-backed) is not a boundary
# crossing — both sides resolve to the gc family.
val warnings = check_gc_boundary_imports(
    "std.gc_async_mut.task",
    ["std.gpu"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### resolve_gc_alias rewrites gpu alias to effective gc family path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = resolve_gc_alias("std.gpu")
expect(resolved).to_contain("gc_async_mut")

val resolved2 = resolve_gc_alias("std.nogc_async_mut.gpu")
expect(resolved2).to_contain("gc_async_mut")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/gc_boundary_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc boundary semantic checker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
