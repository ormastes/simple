# Gc Parity Specification

> <details>

<!-- sdn-diagram:id=gc_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Parity Specification

## Scenarios

### Interpreter GC Parity

#### family extraction from resolved path

#### extracts nogc_sync_mut from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/nogc_sync_mut/fs.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_sync_mut")
```

</details>

#### extracts nogc_async_mut from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/nogc_async_mut/thread.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_async_mut")
```

</details>

#### extracts gc_async_mut from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/gc_async_mut/cuda.spl"
val family = _extract_family(path)
expect(family).to_equal("gc_async_mut")
```

</details>

#### extracts nogc_async_immut from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/nogc_async_immut/persistent.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_async_immut")
```

</details>

#### extracts common from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/common/text.spl"
val family = _extract_family(path)
expect(family).to_equal("common")
```

</details>

#### extracts nogc_async_mut_noalloc before nogc_async_mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/nogc_async_mut_noalloc/memory.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_async_mut_noalloc")
```

</details>

#### returns empty for unknown path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/cli/main.spl"
val family = _extract_family(path)
expect(family).to_equal("")
```

</details>

#### is_nogc_family classification

#### nogc_sync_mut is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_nogc("nogc_sync_mut")).to_equal(true)
```

</details>

#### nogc_async_mut is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_nogc("nogc_async_mut")).to_equal(true)
```

</details>

#### nogc_async_mut_noalloc is nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_nogc("nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### gc_async_mut is not nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_nogc("gc_async_mut")).to_equal(false)
```

</details>

#### common is not nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_nogc("common")).to_equal(false)
```

</details>

#### is_gc_family classification

#### gc_async_mut is gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_gc("gc_async_mut")).to_equal(true)
```

</details>

#### nogc_sync_mut is not gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_gc("nogc_sync_mut")).to_equal(false)
```

</details>

#### common is not gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_gc("common")).to_equal(false)
```

</details>

#### is_noalloc_family classification

#### nogc_async_mut_noalloc is noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_noalloc("nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### nogc_sync_mut is not noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_noalloc("nogc_sync_mut")).to_equal(false)
```

</details>

#### gc_async_mut is not noalloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_is_noalloc("gc_async_mut")).to_equal(false)
```

</details>

#### should_warn_gc_boundary

#### warns when nogc imports gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn("nogc_sync_mut", "gc_async_mut")
expect(result).to_equal(true)
```

</details>

#### warns when nogc_async imports gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn("nogc_async_mut", "gc_async_mut")
expect(result).to_equal(true)
```

</details>

#### does not warn when gc imports nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn("gc_async_mut", "nogc_sync_mut")
expect(result).to_equal(false)
```

</details>

#### does not warn for same family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn("nogc_sync_mut", "nogc_sync_mut")
expect(result).to_equal(false)
```

</details>

#### does not warn when common imports anything

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn("common", "gc_async_mut")
expect(result).to_equal(false)
```

</details>

#### does not warn when anything imports common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn("nogc_sync_mut", "common")
expect(result).to_equal(false)
```

</details>

#### warns when noalloc imports allocating nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn_noalloc("nogc_async_mut_noalloc", "nogc_sync_mut")
expect(result).to_equal(true)
```

</details>

#### warns when noalloc imports gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn_noalloc("nogc_async_mut_noalloc", "gc_async_mut")
expect(result).to_equal(true)
```

</details>

#### does not warn for noalloc importing common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _should_warn_noalloc("nogc_async_mut_noalloc", "common")
expect(result).to_equal(false)
```

</details>

#### interpreter vs compiler family detection consistency

#### both detect nogc_sync_mut as nogc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path_family = _extract_family("src/lib/nogc_sync_mut/fs.spl")
expect(_is_nogc(path_family)).to_equal(true)
```

</details>

#### both detect gc_async_mut as gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path_family = _extract_family("src/lib/gc_async_mut/cuda.spl")
expect(_is_gc(path_family)).to_equal(true)
```

</details>

#### both detect noalloc correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path_family = _extract_family("src/lib/nogc_async_mut_noalloc/mem.spl")
expect(_is_noalloc(path_family)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/gc_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Interpreter GC Parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
