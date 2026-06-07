# Treesitter Visibility Specification

> 1. var ts = TreeSitter new

<!-- sdn-diagram:id=treesitter_visibility_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_visibility_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_visibility_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_visibility_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Visibility Specification

## Scenarios

### TreeSitter Scoped Visibility Parsing

#### parses scoped visibility on top-level declarations

1. var ts = TreeSitter new
   - Expected: outline.functions.len() equals `2`
   - Expected: outline.functions[0].visibility equals `Visibility.Peer`
   - Expected: outline.functions[0].is_public is false
   - Expected: outline.enums[0].visibility equals `Visibility.Up`
   - Expected: outline.constants[0].visibility equals `Visibility.Internal`
   - Expected: outline.constants[1].visibility equals `Visibility.Package`
   - Expected: outline.functions[1].visibility equals `Visibility.Private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "pub(peer) fn peer_fn():\n    0\n\npub(up) enum ParentOnly:\n    Ready\n\npub(friend) val internal_value: i64 = 1\npub(package) val package_value: i64 = 2\npri fn local_fn():\n    0\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()

expect(outline.functions.len()).to_equal(2)
expect(outline.functions[0].visibility).to_equal(Visibility.Peer)
expect(outline.functions[0].is_public).to_equal(false)
expect(outline.enums[0].visibility).to_equal(Visibility.Up)
expect(outline.constants[0].visibility).to_equal(Visibility.Internal)
expect(outline.constants[1].visibility).to_equal(Visibility.Package)
expect(outline.functions[1].visibility).to_equal(Visibility.Private)
```

</details>

#### parses scoped visibility on class and impl members

1. var ts = TreeSitter new
   - Expected: outline.classes.len() equals `1`
   - Expected: outline.classes[0].methods.len() equals `1`
   - Expected: outline.classes[0].methods[0].visibility equals `Visibility.Peer`
   - Expected: outline.classes[0].fields[0].visibility equals `Visibility.Up`
   - Expected: outline.impls.len() equals `1`
   - Expected: outline.impls[0].methods.len() equals `1`
   - Expected: outline.impls[0].methods[0].visibility equals `Visibility.Package`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "class Widget:\n    pub(peer) fn peer_method():\n        0\n    pub(up) helper: i64\n\nimpl Widget:\n    pub(package) fn package_method():\n        0\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()

expect(outline.classes.len()).to_equal(1)
expect(outline.classes[0].methods.len()).to_equal(1)
expect(outline.classes[0].methods[0].visibility).to_equal(Visibility.Peer)
expect(outline.classes[0].fields[0].visibility).to_equal(Visibility.Up)
expect(outline.impls.len()).to_equal(1)
expect(outline.impls[0].methods.len()).to_equal(1)
expect(outline.impls[0].methods[0].visibility).to_equal(Visibility.Package)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_visibility_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TreeSitter Scoped Visibility Parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
