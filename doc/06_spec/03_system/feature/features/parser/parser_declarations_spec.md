# Parser Declarations Specification

> Tests covering Struct Declaration Parsing, Enum Declaration Parsing, Class Declaration Parsing, Trait Declaration Parsing, Module Declaration Parsing, Import Declaration Parsing, Type Alias Declaration Parsing, Variable Declaration Parsing, Impl Block Parsing, Attribute Declaration Parsing.

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

- parses struct with fields
   - Expected: p.sum() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct with fields")
val p = ParserDeclPoint(x: 2, y: 3)
expect(p.sum()).to_equal(5)
```

</details>

#### parses struct with single field

- parses struct with single field
   - Expected: single.label equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct with single field")
val single = ParserDeclSingle(label: "only")
expect(single.label).to_equal("only")
```

</details>

#### parses empty struct

- parses empty struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses empty struct")
val empty = ParserDeclEmpty(marker: true)
assert_true(empty.marker)
```

</details>

#### generic structs

#### parses generic struct

- parses generic struct
   - Expected: boxed.value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses generic struct")
val boxed = ParserDeclBox<i64>.create(42)
expect(boxed.value).to_equal(42)
```

</details>

#### parses multi-param generic struct

- parses multi-param generic struct
   - Expected: pair.key + ":" + pair.value.to_text() equals `answer:42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multi-param generic struct")
val pair = ParserDeclPair<text, i64>(key: "answer", value: 42)
expect(pair.key + ":" + pair.value.to_text()).to_equal("answer:42")
```

</details>

#### nested structs

#### parses struct with struct field

- parses struct with struct field
   - Expected: segment.total() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct with struct field")
val segment = ParserDeclSegment(start: ParserDeclPoint(x: 1, y: 2), finish: ParserDeclPoint(x: 3, y: 4))
expect(segment.total()).to_equal(10)
```

</details>

### Enum Declaration Parsing

#### simple enums

#### parses enum without data

- parses enum without data
   - Expected: ParserDeclColor.Red.label() equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum without data")
expect(ParserDeclColor.Red.label()).to_equal("red")
```

</details>

#### parses enum comparison

- parses enum comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum comparison")
assert_true(ParserDeclColor.Green == ParserDeclColor.Green)
```

</details>

#### enums with data

#### parses enum with tuple variant

- parses enum with tuple variant
   - Expected: n equals `7`
   - Expected: "tuple variant did not match" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum with tuple variant")
val value = ParserDeclPayload.Number(7)
if val ParserDeclPayload.Number(n) = value:
    expect(n).to_equal(7)
else:
    expect("tuple variant did not match").to_equal("")
```

</details>

#### parses enum with struct variant

- parses enum with struct variant
   - Expected: label equals `items`
   - Expected: n equals `3`
   - Expected: "struct variant did not match" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum with struct variant")
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

- parses enum in match
   - Expected: label equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum in match")
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

- parses class with fields
   - Expected: counter.current() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses class with fields")
val counter = ParserDeclCounter(count: 2)
expect(counter.current()).to_equal(2)
```

</details>

#### parses class with methods

- parses class with methods
   - Expected: counter.current() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses class with methods")
var counter = ParserDeclCounter(count: 2)
counter.bump()
expect(counter.current()).to_equal(3)
```

</details>

#### class inheritance

#### parses class with trait impl

- parses class with trait impl
   - Expected: p.display() equals `6,7`
   - Expected: parser_declaration_source_status("trait_impl", "trait DisplayFixture:\n    fn display() -> text\n\nstruct DisplayPoint:\n    x: i64\n\nimpl DisplayFixture for DisplayPoint:\n    fn display() -> text:\n        \"displayed\"") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses class with trait impl")
val p = ParserDeclPoint(x: 6, y: 7)
expect(p.display()).to_equal("6,7")
expect(parser_declaration_source_status("trait_impl", "trait DisplayFixture:\n    fn display() -> text\n\nstruct DisplayPoint:\n    x: i64\n\nimpl DisplayFixture for DisplayPoint:\n    fn display() -> text:\n        \"displayed\"")).to_equal("pass")
```

</details>

### Trait Declaration Parsing

#### basic traits

#### parses trait with method

- parses trait with method
   - Expected: p.display() equals `8,9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait with method")
val p = ParserDeclPoint(x: 8, y: 9)
expect(p.display()).to_equal("8,9")
```

</details>

#### parses trait with default method

- parses trait with default method
   - Expected: parser_declaration_source_status("trait_default", "trait NamedFixture:\n    fn name() -> text:\n        \"default\"") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait with default method")
expect(parser_declaration_source_status("trait_default", "trait NamedFixture:\n    fn name() -> text:\n        \"default\"")).to_equal("pass")
```

</details>

#### trait bounds

#### parses trait extending trait

- parses trait extending trait
   - Expected: parser_declaration_source_status("trait_extends", "trait BaseFixture:\n    fn display() -> text\n\ntrait PrettyFixture: BaseFixture:\n    fn pretty() -> text") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait extending trait")
expect(parser_declaration_source_status("trait_extends", "trait BaseFixture:\n    fn display() -> text\n\ntrait PrettyFixture: BaseFixture:\n    fn pretty() -> text")).to_equal("pass")
```

</details>

### Module Declaration Parsing

#### inline modules

#### parses inline module

- parses inline module
   - Expected: parser_declaration_source_status("mod_simple", "mod parser_decl_fixture") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses inline module")
expect(parser_declaration_source_status("mod_simple", "mod parser_decl_fixture")).to_equal("pass")
```

</details>

#### parses nested modules

- parses nested modules
   - Expected: parser_declaration_source_status("mod_nested", "mod parser_decl_fixture.nested") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested modules")
expect(parser_declaration_source_status("mod_nested", "mod parser_decl_fixture.nested")).to_equal("pass")
```

</details>

#### module items

#### parses module with multiple items

- parses module with multiple items
   - Expected: parser_declaration_source_status("mod_items", "mod parser_decl_fixture\nexport use parser_decl_fixture.{x, y}") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses module with multiple items")
expect(parser_declaration_source_status("mod_items", "mod parser_decl_fixture\nexport use parser_decl_fixture.{x, y}")).to_equal("pass")
```

</details>

### Import Declaration Parsing

#### parses simple import

- parses simple import
   - Expected: parser_declaration_source_status("use_simple", "use std.spec") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple import")
expect(parser_declaration_source_status("use_simple", "use std.spec")).to_equal("pass")
```

</details>

#### parses specific import

- parses specific import
   - Expected: parser_declaration_source_status("use_specific", "use std.spec." + "{" + "expect" + "}") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses specific import")
expect(parser_declaration_source_status("use_specific", "use std.spec." + "{" + "expect" + "}")).to_equal("pass")
```

</details>

#### parses multiple imports

- parses multiple imports
   - Expected: parser_declaration_source_status("use_multiple", "use std.spec." + "{" + "describe, expect" + "}") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple imports")
expect(parser_declaration_source_status("use_multiple", "use std.spec." + "{" + "describe, expect" + "}")).to_equal("pass")
```

</details>

### Type Alias Declaration Parsing

#### parses simple type alias

- parses simple type alias
   - Expected: boxed.value equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple type alias")
val boxed = ParserDeclIntBox.create(11)
expect(boxed.value).to_equal(11)
```

</details>

#### parses generic type alias

- parses generic type alias
   - Expected: aliased.value equals `typed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses generic type alias")
val aliased = ParserDeclBox<text>.create("typed")
expect(aliased.value).to_equal("typed")
```

</details>

#### parses complex type alias

- parses complex type alias
   - Expected: pair.value.sum() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses complex type alias")
val pair = ParserDeclTextPoint(key: "origin", value: ParserDeclPoint(x: 0, y: 0))
expect(pair.value.sum()).to_equal(0)
```

</details>

### Variable Declaration Parsing

#### immutable variables

#### parses val declaration

- parses val declaration
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses val declaration")
val x = 42
expect(x).to_equal(42)
```

</details>

#### parses val with type annotation

- parses val with type annotation
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses val with type annotation")
val x: i64 = 42
expect(x).to_equal(42)
```

</details>

#### mutable variables

#### parses var declaration

- parses var declaration
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses var declaration")
var x = 0
x = 42
expect(x).to_equal(42)
```

</details>

#### parses var with type annotation

- parses var with type annotation
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses var with type annotation")
var x: i64 = 0
x = 42
expect(x).to_equal(42)
```

</details>

#### let bindings

#### parses let declaration

- parses let declaration
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses let declaration")
let x = 42
expect(x).to_equal(42)
```

</details>

#### parses let with destructuring

- parses let with destructuring
   - Expected: a + b equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses let with destructuring")
let (a, b) = (1, 2)
expect(a + b).to_equal(3)
```

</details>

### Impl Block Parsing

#### parses impl block for struct

- parses impl block for struct
   - Expected: ParserDeclColor.Red.label() equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl block for struct")
expect(ParserDeclColor.Red.label()).to_equal("red")
```

</details>

#### parses impl block for trait

- parses impl block for trait
   - Expected: p.display() equals `4,5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl block for trait")
val p = ParserDeclPoint(x: 4, y: 5)
expect(p.display()).to_equal("4,5")
```

</details>

### Attribute Declaration Parsing

#### documents SPipe @cover metadata is not a compiler function attribute

- documents SPipe @cover metadata is not a compiler function attribute
   - Expected: parser_declaration_metadata_skip_status("attr_cover_metadata", "@cover src/compiler/10.frontend/parser_types.spl 80%\nfn attr_fixture(): pass", "expected Fn") equals `skip: spipe-metadata-not-compiler-attribute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents SPipe @cover metadata is not a compiler function attribute")
expect(parser_declaration_metadata_skip_status("attr_cover_metadata", "@cover src/compiler/10.frontend/parser_types.spl 80%\nfn attr_fixture(): pass", "expected Fn")).to_equal("skip: spipe-metadata-not-compiler-attribute")
```

</details>

#### documents SPipe @when metadata is not a compiler function attribute

- documents SPipe @when metadata is not a compiler function attribute
   - Expected: parser_declaration_metadata_skip_status("attr_when_metadata", "@when(target = \"test\")\nfn attr_fixture(): pass", "variable `when` not found") equals `skip: spipe-metadata-not-compiler-attribute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents SPipe @when metadata is not a compiler function attribute")
expect(parser_declaration_metadata_skip_status("attr_when_metadata", "@when(target = \"test\")\nfn attr_fixture(): pass", "variable `when` not found")).to_equal("skip: spipe-metadata-not-compiler-attribute")
```

</details>

#### documents multiple SPipe metadata lines are not compiler attributes

- documents multiple SPipe metadata lines are not compiler attributes
   - Expected: parser_declaration_metadata_skip_status("attr_multiple_metadata", "@cover a 80%\n@when(target = \"test\")\nfn attr_fixture(): pass", "expected Fn") equals `skip: spipe-metadata-not-compiler-attribute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents multiple SPipe metadata lines are not compiler attributes")
expect(parser_declaration_metadata_skip_status("attr_multiple_metadata", "@cover a 80%\n@when(target = \"test\")\nfn attr_fixture(): pass", "expected Fn")).to_equal("skip: spipe-metadata-not-compiler-attribute")
```

</details>

#### parses attribute on struct

- parses attribute on struct
   - Expected: parser_declaration_source_status("attr_derive_struct", "@derive(Debug)\nstruct AttrFixture:\n    value: i64") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses attribute on struct")
expect(parser_declaration_source_status("attr_derive_struct", "@derive(Debug)\nstruct AttrFixture:\n    value: i64")).to_equal("pass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/parser/parser_declarations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Struct Declaration Parsing, Enum Declaration Parsing, Class Declaration Parsing, Trait Declaration Parsing, Module Declaration Parsing, Import Declaration Parsing, Type Alias Declaration Parsing, Variable Declaration Parsing, Impl Block Parsing, Attribute Declaration Parsing.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `acc913340806d70d75e6ade8a1a202a331cfd3b96612f9aea3237acd4d08a07b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `acc913340806d70d75e6ade8a1a202a331cfd3b96612f9aea3237acd4d08a07b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `acc913340806d70d75e6ade8a1a202a331cfd3b96612f9aea3237acd4d08a07b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/features/parser/parser_declarations_spec.spl
mirror: doc/06_spec/03_system/feature/features/parser/parser_declarations_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/parser/parser_declarations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/parser/parser_declarations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/parser/parser_declarations_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/features/parser/parser_declarations_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses struct with fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/parser/parser_declarations_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses struct with single field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/parser/parser_declarations_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses empty struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
