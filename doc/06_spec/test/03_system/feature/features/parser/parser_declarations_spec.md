# Parser Declarations Specification

> <details>

<!-- sdn-diagram:id=parser_declarations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_declarations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_declarations_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_declarations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Declarations Specification

## Scenarios

### Struct Declaration Parsing

#### basic structs

#### parses struct with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ParserDeclPoint(x: 2, y: 3)
expect(p.sum()).to_equal(5)
```

</details>

#### parses struct with single field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single = ParserDeclSingle(label: "only")
expect(single.label).to_equal("only")
```

</details>

#### parses empty struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ParserDeclEmpty(marker: true)
expect(empty.marker)
```

</details>

#### generic structs

#### parses generic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxed = ParserDeclBox<i64>.create(42)
expect(boxed.value).to_equal(42)
```

</details>

#### parses multi-param generic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = ParserDeclPair<text, i64>(key: "answer", value: 42)
expect(pair.key + ":" + pair.value.to_text()).to_equal("answer:42")
```

</details>

#### nested structs

#### parses struct with struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val segment = ParserDeclSegment(start: ParserDeclPoint(x: 1, y: 2), finish: ParserDeclPoint(x: 3, y: 4))
expect(segment.total()).to_equal(10)
```

</details>

### Enum Declaration Parsing

#### simple enums

#### parses enum without data

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ParserDeclColor.Red.label()).to_equal("red")
```

</details>

#### parses enum comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ParserDeclColor.Green == ParserDeclColor.Green)
```

</details>

#### enums with data

#### parses enum with tuple variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = ParserDeclPayload.Number(7)
if val ParserDeclPayload.Number(n) = value:
    expect(n).to_equal(7)
else:
    expect("tuple variant did not match").to_equal("")
```

</details>

#### parses enum with struct variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = ParserDeclPayload.Named(name: "items", count: 3)
if val ParserDeclPayload.Named(name: label, count: n) = value:
    expect(label).to_equal("items")
    expect(n).to_equal(3)
else:
    expect("struct variant did not match").to_equal("")
```

</details>

#### enum matching

#### parses enum in match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = ParserDeclColor.Blue
val label = match value:
    case Red: "red"
    case Green: "green"
    case Blue: "blue"
expect(label).to_equal("blue")
```

</details>

### Class Declaration Parsing

#### basic classes

#### parses class with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counter = ParserDeclCounter(count: 2)
expect(counter.current()).to_equal(2)
```

</details>

#### parses class with methods

1. var counter = ParserDeclCounter
2. counter bump
   - Expected: counter.current() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = ParserDeclCounter(count: 2)
counter.bump()
expect(counter.current()).to_equal(3)
```

</details>

#### class inheritance

#### parses class with trait impl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ParserDeclPoint(x: 6, y: 7)
expect(p.display()).to_equal("6,7")
expect(parser_declaration_source_status("trait_impl", "trait DisplayFixture:\n    fn display() -> text\n\nstruct DisplayPoint:\n    x: i64\n\nimpl DisplayFixture for DisplayPoint:\n    fn display() -> text:\n        \"displayed\"")).to_equal("pass")
```

</details>

### Trait Declaration Parsing

#### basic traits

#### parses trait with method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ParserDeclPoint(x: 8, y: 9)
expect(p.display()).to_equal("8,9")
```

</details>

#### parses trait with default method

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("trait_default", "trait NamedFixture:\n    fn name() -> text:\n        \"default\"")).to_equal("pass")
```

</details>

#### trait bounds

#### parses trait extending trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("trait_extends", "trait BaseFixture:\n    fn display() -> text\n\ntrait PrettyFixture: BaseFixture:\n    fn pretty() -> text")).to_equal("pass")
```

</details>

### Module Declaration Parsing

#### inline modules

#### parses inline module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("mod_simple", "mod parser_decl_fixture")).to_equal("pass")
```

</details>

#### parses nested modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("mod_nested", "mod parser_decl_fixture.nested")).to_equal("pass")
```

</details>

#### module items

#### parses module with multiple items

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("mod_items", "mod parser_decl_fixture\nexport use parser_decl_fixture.{x, y}")).to_equal("pass")
```

</details>

### Import Declaration Parsing

#### parses simple import

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("use_simple", "use std.spec")).to_equal("pass")
```

</details>

#### parses specific import

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("use_specific", "use std.spec." + "{" + "expect" + "}")).to_equal("pass")
```

</details>

#### parses multiple imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("use_multiple", "use std.spec." + "{" + "describe, expect" + "}")).to_equal("pass")
```

</details>

### Type Alias Declaration Parsing

#### parses simple type alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxed = ParserDeclIntBox.create(11)
expect(boxed.value).to_equal(11)
```

</details>

#### parses generic type alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aliased = ParserDeclBox<text>.create("typed")
expect(aliased.value).to_equal("typed")
```

</details>

#### parses complex type alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = ParserDeclTextPoint(key: "origin", value: ParserDeclPoint(x: 0, y: 0))
expect(pair.value.sum()).to_equal(0)
```

</details>

### Variable Declaration Parsing

#### immutable variables

#### parses val declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect(x).to_equal(42)
```

</details>

#### parses val with type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
expect(x).to_equal(42)
```

</details>

#### mutable variables

#### parses var declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
x = 42
expect(x).to_equal(42)
```

</details>

#### parses var with type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: i64 = 0
x = 42
expect(x).to_equal(42)
```

</details>

#### let bindings

#### parses let declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 42
expect(x).to_equal(42)
```

</details>

#### parses let with destructuring

1. let
   - Expected: a + b equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let (a, b) = (1, 2)
expect(a + b).to_equal(3)
```

</details>

### Impl Block Parsing

#### parses impl block for struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ParserDeclColor.Red.label()).to_equal("red")
```

</details>

#### parses impl block for trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ParserDeclPoint(x: 4, y: 5)
expect(p.display()).to_equal("4,5")
```

</details>

### Attribute Declaration Parsing

#### documents SPipe @cover metadata is not a compiler function attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_metadata_skip_status("attr_cover_metadata", "@cover src/compiler/10.frontend/parser_types.spl 80%\nfn attr_fixture(): pass", "expected Fn")).to_equal("skip: spipe-metadata-not-compiler-attribute")
```

</details>

#### documents SPipe @when metadata is not a compiler function attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_metadata_skip_status("attr_when_metadata", "@when(target = \"test\")\nfn attr_fixture(): pass", "variable `when` not found")).to_equal("skip: spipe-metadata-not-compiler-attribute")
```

</details>

#### documents multiple SPipe metadata lines are not compiler attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_metadata_skip_status("attr_multiple_metadata", "@cover a 80%\n@when(target = \"test\")\nfn attr_fixture(): pass", "expected Fn")).to_equal("skip: spipe-metadata-not-compiler-attribute")
```

</details>

#### parses attribute on struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parser_declaration_source_status("attr_derive_struct", "@derive(Debug)\nstruct AttrFixture:\n    value: i64")).to_equal("pass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/parser/parser_declarations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Struct Declaration Parsing
- Enum Declaration Parsing
- Class Declaration Parsing
- Trait Declaration Parsing
- Module Declaration Parsing
- Import Declaration Parsing
- Type Alias Declaration Parsing
- Variable Declaration Parsing
- Impl Block Parsing
- Attribute Declaration Parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
