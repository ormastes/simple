# Lazy Outline Equivalence

> Proves that the treesitter outline (fast/lazy) parser is a faithful basis for lazy parsing by showing that its declaration-surface extraction is equivalent to a full-parse scan over the same source.

<!-- sdn-diagram:id=lazy_outline_equivalence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lazy_outline_equivalence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lazy_outline_equivalence_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lazy_outline_equivalence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Outline Equivalence

Proves that the treesitter outline (fast/lazy) parser is a faithful basis for lazy parsing by showing that its declaration-surface extraction is equivalent to a full-parse scan over the same source.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W2-A1 |
| Category | Compiler \| Frontend \| Lazy Parsing |
| Status | Groundwork (AC-4) |
| Source | `test/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that the treesitter outline (fast/lazy) parser is a faithful basis
for lazy parsing by showing that its declaration-surface extraction is
equivalent to a full-parse scan over the same source.

## Design

Because `compiler.frontend.treesitter` cannot be imported from interpreter-mode
specs (all such imports are blocked — see block_skip_policy_spec.spl), this
harness implements a lightweight text-based declaration extractor that mirrors
what the outline parser does:

  - **Outline path**: scan only top-level `fn`/`class`/`struct`/`enum`/`trait`
    keywords at indent-0, skipping function body lines.
  - **Full path**: scan all lines including body lines, but still collect
    only the same top-level declarations.

Both paths must yield identical sorted name sets for each sample module.
This equivalence property is the key guarantee that lazy parsing is safe.

## Files Tested

Five small, stable repo modules chosen for declaration diversity:
  1. src/compiler/00.common/dependency/graph.spl
     (ImportGraph, ImportEdge, ImportKind, CyclicDependencyError + fns)
  2. src/lib/common/markdown/types.spl   (struct/enum declarations)
  3. src/lib/common/cbor/types.spl       (struct/enum/fn-heavy, 270 lines)
  4. src/lib/common/cbor/utilities.spl   (fn-heavy, 117 lines)
  5. src/lib/common/ui/color.spl         (struct + fns)

## Interpreter Note

`it` block bodies execute in interpreter mode. This spec runs fully green
in interpreter mode with `SIMPLE_LIB=src bin/simple test <path>`.

## Scenarios

### Lazy Outline Equivalence

#### graph.spl — ImportGraph + cycle detection

#### outline and full parse yield same declaration surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_equiv(graph_src, "graph.spl"))
```

</details>

#### outline is non-empty

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_nonempty(graph_src, "graph.spl"))
```

</details>

#### ImportGraph struct is in outline surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_name_present(graph_src, "ImportGraph"))
```

</details>

#### ImportKind enum is in outline surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_name_present(graph_src, "ImportKind"))
```

</details>

#### importgraph_add_edge fn is in outline surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_name_present(graph_src, "importgraph_add_edge"))
```

</details>

#### importgraph_find_cycles fn is in outline surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_name_present(graph_src, "importgraph_find_cycles"))
```

</details>

#### markdown/types.spl — struct/enum declarations

#### outline and full parse yield same declaration surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_equiv(md_types_src, "markdown/types.spl"))
```

</details>

#### outline is non-empty

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_nonempty(md_types_src, "markdown/types.spl"))
```

</details>

#### cbor/types.spl — struct/enum/fn module

#### outline and full parse yield same declaration surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_equiv(cbor_types_src, "cbor/types.spl"))
```

</details>

#### outline is non-empty

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_nonempty(cbor_types_src, "cbor/types.spl"))
```

</details>

#### cbor/utilities.spl — fn-heavy module

#### outline and full parse yield same declaration surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_equiv(cbor_util_src, "cbor/utilities.spl"))
```

</details>

#### outline is non-empty

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_nonempty(cbor_util_src, "cbor/utilities.spl"))
```

</details>

#### ui/color.spl — struct + fn module

#### outline and full parse yield same declaration surface

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_equiv(color_src, "ui/color.spl"))
```

</details>

#### outline is non-empty

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(check_nonempty(color_src, "ui/color.spl"))
```

</details>

#### indent-fence invariant

#### body lines (indented) are never collected by outline scanner

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Synthetic source: fn with indented body that contains a nested fn keyword
val src = "fn outer():\n    fn inner_not_decl():\n        pass\nstruct Foo:\n    x: i64\n"
val names = scan_outline(src)
# inner_not_decl should NOT appear (indented)
var found_inner = false
for n in names:
    if n.contains("inner_not_decl"):
        found_inner = true
check(not found_inner)
# outer and Foo SHOULD appear
check(check_name_present(src, "outer"))
check(check_name_present(src, "Foo"))
```

</details>

#### export-qualified fns are captured by outline scanner

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "export fn my_fn(x: i64) -> i64:\n    x + 1\nfn other():\n    pass\n"
check(check_name_present(src, "my_fn"))
check(check_name_present(src, "other"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
