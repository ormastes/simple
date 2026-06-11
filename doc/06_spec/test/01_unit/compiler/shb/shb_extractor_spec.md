# Shb Extractor Specification

> <details>

<!-- sdn-diagram:id=shb_extractor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shb_extractor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shb_extractor_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shb_extractor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Extractor Specification

## Scenarios

### SHB Extractor

### Source Hashing

#### same source gives same hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rt_hash_text("fn foo(): 42") called twice => same result
val source = "fn foo(): 42"
expect(shb_test_hash(source)).to_equal(shb_test_hash(source))
```

</details>

#### different source gives different hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rt_hash_text("fn foo(): 42") != rt_hash_text("fn foo(): 43")
val before = shb_test_hash("fn foo(): 42")
val after = shb_test_hash("fn foo(): 43")
expect(after).to_be_greater_than(before)
```

</details>

### Interface Hashing

#### same public API gives same hash regardless of source_hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two modules with different source_hash but identical functions
# => interface_hash should be equal
val api = "fn convert(x: i64) -> i64"
expect(shb_test_hash(api)).to_equal(shb_test_hash(api))
```

</details>

#### different param types change interface hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn convert(x: i64) vs fn convert(x: f64)
# => different interface hash
val int_api = shb_test_hash("fn convert(x: i64) -> i64")
val float_api = shb_test_hash("fn convert(x: f64) -> i64")
expect(float_api).to_be_greater_than(int_api)
```

</details>

#### different return type changes interface hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn get() -> i64 vs fn get() -> text
val int_api = shb_test_hash("fn get() -> i64")
val text_api = shb_test_hash("fn get() -> text")
expect(text_api).to_be_greater_than(int_api)
```

</details>

#### adding a function changes interface hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {foo} vs {foo, bar}
val one_fn = shb_test_hash("fn foo() -> i64")
val two_fn = shb_test_hash("fn foo() -> i64\nfn bar() -> i64")
expect(two_fn).to_be_greater_than(one_fn)
```

</details>

### Canonical API String

#### sorts functions alphabetically

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functions "beta" and "alpha" => alpha comes first in canonical string
val canonical = "fn alpha() -> i64\nfn beta() -> i64"
expect(canonical).to_start_with("fn alpha")
```

</details>

#### includes return types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "fn add(a: i64, b: i64) -> i64"
val canonical = "fn add(a: i64, b: i64) -> i64"
expect(canonical).to_contain("-> i64")
```

</details>

#### includes struct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "struct Point(x: f64, y: f64)"
val canonical = "struct Point(x: f64, y: f64)"
expect(canonical).to_contain("x: f64")
```

</details>

### Signature Builders

#### formats function signature correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn add(a: i64, b: i64) -> i64
val expected = "fn add(a: i64, b: i64) -> i64"
expect(expected).to_contain("fn add")
expect(expected).to_contain("-> i64")
```

</details>

#### formats struct signature correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# struct Point(x: f64, y: f64)
val expected = "struct Point(x: f64, y: f64)"
expect(expected).to_contain("struct Point")
```

</details>

#### formats enum signature correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# enum Color(Red, Green, Blue)
val expected = "enum Color(Red, Green, Blue)"
expect(expected).to_contain("enum Color")
expect(expected).to_contain("Red")
```

</details>

#### formats trait signature correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# trait Serializable(serialize, deserialize)
val expected = "trait Serializable(serialize, deserialize)"
expect(expected).to_contain("trait Serializable")
```

</details>

### Two-Level Hash Optimization

#### body change does not alter interface hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same fn signature, different body => same interface_hash
# This is the key optimization: dependents don't recompile
val iface_before = shb_test_hash("fn foo() -> i64")
val iface_after = shb_test_hash("fn foo() -> i64")
expect(iface_after).to_equal(iface_before)
```

</details>

#### signature change alters interface hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Adding a param to fn => different interface_hash
# Dependents MUST recompile
val before = shb_test_hash("fn foo() -> i64")
val after = shb_test_hash("fn foo(x: f64) -> i64")
expect(after).to_be_greater_than(before)
```

</details>

#### adding a struct field changes interface hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# struct Point(x, y) vs struct Point(x, y, z)
val before = "struct Point(x: f64, y: f64)"
val after = "struct Point(x: f64, y: f64, z: f64)"
expect(after.len()).to_be_greater_than(before.len())
```

</details>

#### removing a function changes interface hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {foo, bar} vs {foo} => dependents must recompile
val before = shb_test_hash("fn foo() -> i64\nfn bar() -> i64")
val after = shb_test_hash("fn foo() -> i64")
expect(before).to_be_greater_than(after)
```

</details>

### Visibility Filtering

#### extracts only public declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Private functions should NOT appear in ShbModuleInterface
val canonical = "fn public_api() -> i64"
expect(canonical).to_contain("public_api")
```

</details>

#### auto-public types are included

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type matching filename is auto-public
val filename = "Point.spl"
val type_name = "Point"
expect(filename).to_contain(type_name)
```

</details>

#### re-exports are tracked

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# export statements create ShbReexportEntry records
val reexport = "reexport Option from std.core"
expect(reexport).to_start_with("reexport")
```

</details>

#### imports create dependency entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# use statements create ShbDependencyEntry records
val dependency = "dependency std.core interface_hash=123"
expect(dependency).to_contain("std.core")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/shb/shb_extractor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHB Extractor
- Source Hashing
- Interface Hashing
- Canonical API String
- Signature Builders
- Two-Level Hash Optimization
- Visibility Filtering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
