# Gc Boundary Enforcement Specification

> <details>

<!-- sdn-diagram:id=gc_boundary_enforcement_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_boundary_enforcement_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_boundary_enforcement_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_boundary_enforcement_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Boundary Enforcement Specification

## Scenarios

### GC Boundary Enforcement

#### family prefix classification — is_nogc_family

#### classifies nogc_sync_mut as nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_nogc_family("nogc_sync_mut")).to_equal(true)
```

</details>

#### classifies nogc_async_mut as nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_nogc_family("nogc_async_mut")).to_equal(true)
```

</details>

#### classifies nogc_async_mut_noalloc as nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_nogc_family("nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### classifies gc_async_mut as not nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_nogc_family("gc_async_mut")).to_equal(false)
```

</details>

#### classifies common as not nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_nogc_family("common")).to_equal(false)
```

</details>

#### strips std. prefix before classifying

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_nogc_family("std.nogc_sync_mut.fs")).to_equal(true)
```

</details>

#### strips lib. prefix before classifying

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_nogc_family("lib.nogc_async_mut.thread")).to_equal(true)
```

</details>

#### family prefix classification — is_gc_family

#### classifies gc_async_mut as gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_gc_family("gc_async_mut")).to_equal(true)
```

</details>

#### classifies nogc_sync_mut as not gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_gc_family("nogc_sync_mut")).to_equal(false)
```

</details>

#### classifies common as not gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_gc_family("common")).to_equal(false)
```

</details>

#### classifies empty string as not gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_gc_family("")).to_equal(false)
```

</details>

#### family prefix classification — is_noalloc_family

#### classifies nogc_async_mut_noalloc as noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_noalloc_family("nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### classifies nogc_sync_mut as not noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_noalloc_family("nogc_sync_mut")).to_equal(false)
```

</details>

#### classifies gc_async_mut as not noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_noalloc_family("gc_async_mut")).to_equal(false)
```

</details>

#### classifies common as not noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_noalloc_family("common")).to_equal(false)
```

</details>

#### strips std. prefix for noalloc check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(local_is_noalloc_family("std.nogc_async_mut_noalloc.exec")).to_equal(true)
```

</details>

#### cross-family boundary rules — nogc importing gc

#### nogc_sync_mut importing gc_async_mut produces warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_sync_mut.fs",
    ["gc_async_mut.alloc"]
)
expect(warnings.len()).to_equal(1)
```

</details>

#### nogc_async_mut importing gc_async_mut produces warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_async_mut.thread",
    ["gc_async_mut.runtime"]
)
expect(warnings.len()).to_equal(1)
```

</details>

#### warning message identifies the cross-boundary nature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_sync_mut.fs",
    ["gc_async_mut.alloc"]
)
expect(warnings[0].message).to_equal("no-gc imports GC family")
```

</details>

#### nogc importing common produces no warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_sync_mut.fs",
    ["common.text"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### gc importing nogc produces no warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "gc_async_mut.runtime",
    ["nogc_sync_mut.fs"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### common importing gc produces no warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "common.text",
    ["gc_async_mut.alloc"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### common importing nogc produces no warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "common.text",
    ["nogc_sync_mut.fs"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### cross-family boundary rules — noalloc importing allocating

#### noalloc importing gc_async_mut produces warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_async_mut_noalloc.exec",
    ["gc_async_mut.alloc"]
)
expect(warnings.len()).to_equal(1)
```

</details>

#### noalloc importing nogc_sync_mut produces warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_async_mut_noalloc.exec",
    ["nogc_sync_mut.fs"]
)
expect(warnings.len()).to_equal(1)
```

</details>

#### noalloc importing noalloc produces no warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_async_mut_noalloc.exec",
    ["nogc_async_mut_noalloc.memory"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### noalloc importing common produces no warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_async_mut_noalloc.exec",
    ["common.math"]
)
expect(warnings.len()).to_equal(0)
```

</details>

#### multiple imports — warning count

#### two bad imports produce two warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_sync_mut.mod",
    ["gc_async_mut.a", "gc_async_mut.b"]
)
expect(warnings.len()).to_equal(2)
```

</details>

#### one bad one good produce one warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = local_check_gc_boundary_imports(
    "nogc_sync_mut.mod",
    ["gc_async_mut.a", "common.text"]
)
expect(warnings.len()).to_equal(1)
```

</details>

#### no imports produce no warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [text] = []
val warnings = local_check_gc_boundary_imports("nogc_sync_mut.mod", empty)
expect(warnings.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/gc_boundary_enforcement_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GC Boundary Enforcement

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
