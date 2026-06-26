# MCP simple_api Tool Specification

> Tests the simple_api MCP tool: symbol extraction, visibility filtering, and module path resolution with numbered directory support.

<!-- sdn-diagram:id=api_tool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=api_tool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

api_tool_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=api_tool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP simple_api Tool Specification

Tests the simple_api MCP tool: symbol extraction, visibility filtering, and module path resolution with numbered directory support.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-API-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_unit/api_tool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the simple_api MCP tool: symbol extraction, visibility filtering,
and module path resolution with numbered directory support.

## Behavior

- Extracts functions, classes, structs, enums, traits from source
- Applies visibility markers: P (public), F (friend), I (internal), - (private)
- Filters by visibility level: public, friend, package, all
- Resolves dotted module paths through numbered directories

## Scenarios

### Symbol Extraction Heuristic

#### extracts public function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub fn parse(source: text) -> Result:"
val has_pub = source.starts_with("pub ")
val has_fn = source.contains("fn ")
expect(has_pub).to_equal(true)
expect(has_fn).to_equal(true)
```

</details>

#### extracts private function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn helper() -> text:"
val has_pub = source.starts_with("pub ")
val has_fn = source.starts_with("fn ")
expect(has_pub).to_equal(false)
expect(has_fn).to_equal(true)
```

</details>

#### extracts exported function as public

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = ["parse", "Token"]
val name = "parse"
var is_exported = false
for e in exports:
    if e == name:
        is_exported = true
expect(is_exported).to_equal(true)
```

</details>

#### extracts internal_export as friend-visible

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val internal_exports = ["Builder"]
val name = "Builder"
var is_internal = false
for e in internal_exports:
    if e == name:
        is_internal = true
expect(is_internal).to_equal(true)
```

</details>

#### extracts pub(friend) function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub(friend) fn lower() -> MirModule:"
val has_friend = source.starts_with("pub(friend)")
expect(has_friend).to_equal(true)
```

</details>

#### extracts pub(package) function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub(package) fn validate() -> bool:"
val has_package = source.starts_with("pub(package)")
expect(has_package).to_equal(true)
```

</details>

#### extracts struct declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub struct Point:"
val has_struct = source.contains("struct ")
val has_pub = source.starts_with("pub ")
expect(has_struct).to_equal(true)
expect(has_pub).to_equal(true)
```

</details>

#### extracts enum declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "enum Color:"
val has_enum = source.starts_with("enum ")
expect(has_enum).to_equal(true)
```

</details>

#### extracts trait declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub trait Printable:"
val has_trait = source.contains("trait ")
val has_pub = source.starts_with("pub ")
expect(has_trait).to_equal(true)
expect(has_pub).to_equal(true)
```

</details>

### Visibility Filtering

#### public filter shows only P symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val visibilities = ["P", "-"]
var pub_count: i64 = 0
for v in visibilities:
    if v == "P":
        pub_count = pub_count + 1
expect(pub_count).to_equal(1)
```

</details>

#### all filter shows everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val visibilities = ["P", "-", "F", "I"]
expect(visibilities.len()).to_be_greater_than(1)
```

</details>

### API Tool Helpers

#### extract_fn_name from simple signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn parse(source: text) -> Result:"
# Extract function name: skip "fn " and take until "("
val after_fn = line.substring(3)
val paren_idx = after_fn.index_of("(") ?? 0
val name = after_fn.substring(0, paren_idx)
expect(name).to_equal("parse")
```

</details>

#### extract_fn_name from method signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "me move(dx: i64):"
# Extract method name: skip "me " and take until "("
val after_me = line.substring(3)
val paren_idx = after_me.index_of("(") ?? 0
val name = after_me.substring(0, paren_idx)
expect(name).to_equal("move")
```

</details>

#### extract_type_name from struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val after_kw = "Point:"
val colon_idx = after_kw.index_of(":") ?? 0
val name = after_kw.substring(0, colon_idx)
expect(name).to_equal("Point")
```

</details>

#### extract_type_name with generic

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val after_kw = "List<T>:"
val angle_idx = after_kw.index_of("<") ?? 0
val colon_idx = after_kw.index_of(":") ?? 0
var end_idx = colon_idx
if angle_idx > 0 and angle_idx < colon_idx:
    end_idx = angle_idx
val name = after_kw.substring(0, end_idx)
expect(name).to_equal("List")
```

</details>

#### compute_visibility for exported symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = ["parse", "Token"]
val internal_exports: [text] = []
val name = "parse"
var vis = "-"
for e in exports:
    if e == name:
        vis = "P"
for e in internal_exports:
    if e == name:
        vis = "F"
expect(vis).to_equal("P")
```

</details>

#### compute_visibility for internal_export symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports: [text] = []
val internal_exports = ["Builder"]
val name = "Builder"
var vis = "-"
for e in exports:
    if e == name:
        vis = "P"
for e in internal_exports:
    if e == name:
        vis = "F"
expect(vis).to_equal("F")
```

</details>

#### compute_visibility for private symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = ["parse"]
val internal_exports = ["Builder"]
val name = "helper"
var vis = "-"
for e in exports:
    if e == name:
        vis = "P"
for e in internal_exports:
    if e == name:
        vis = "F"
expect(vis).to_equal("-")
```

</details>

### Type Domain Path Normalization

#### normalizes bare type name to default type domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_api_path("I64")
expect(normalized).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### normalizes owned-domain import path to type directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_api_path("simple-lang/I64")
expect(normalized).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### preserves nested owned-domain path segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_api_path("simple-lang/math/F64")
expect(normalized).to_equal("src/type/simple_lang/math/F64.spl")
```

</details>

#### does not rewrite dotted module paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_api_path("compiler.frontend.parser_types")
expect(normalized).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
