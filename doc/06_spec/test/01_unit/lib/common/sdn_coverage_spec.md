# SDN Coverage Specification

> Comprehensive branch-coverage tests for the SDN parser library:

<!-- sdn-diagram:id=sdn_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SDN Coverage Specification

Comprehensive branch-coverage tests for the SDN parser library:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-SDN |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/sdn_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive branch-coverage tests for the SDN parser library:
- `src/lib/common/sdn/` -- SDN value, lexer, parser, document, handler, error

Targets 90%+ branch coverage by exercising both true and false branches of every
conditional in each module.

Split from `parsers_coverage_spec.spl` to avoid memory pressure (404 it-blocks hit 2048MB RSS cap).

## Scenarios

### SDN Value

#### constructors

#### creates null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.null()
expect(v.is_null()).to_equal(true)
```

</details>

#### creates bool true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.bool(true)
expect(v.is_bool()).to_equal(true)
```

</details>

#### creates bool false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.bool(false)
expect(v.is_bool()).to_equal(true)
```

</details>

#### creates int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.int(42)
expect(v.is_int()).to_equal(true)
```

</details>

#### creates float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.float(3.14)
expect(v.is_float()).to_equal(true)
```

</details>

#### creates string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.string("hello")
expect(v.is_string()).to_equal(true)
```

</details>

#### creates array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.array([SdnValue.int(1)])
expect(v.is_array()).to_equal(true)
```

</details>

#### creates empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.empty_array()
expect(v.is_array()).to_equal(true)
```

</details>

#### creates dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.empty_dict()
expect(v.is_dict()).to_equal(true)
```

</details>

#### type checks - negative
_Each type check returns false for other types._

#### is_null false for non-null

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_null()).to_equal(false)
```

</details>

#### is_bool false for non-bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_bool()).to_equal(false)
```

</details>

#### is_int false for non-int

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.string("x").is_int()).to_equal(false)
```

</details>

#### is_float false for non-float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_float()).to_equal(false)
```

</details>

#### is_number true for int

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_number()).to_equal(true)
```

</details>

#### is_number true for float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.float(1.0).is_number()).to_equal(true)
```

</details>

#### is_number false for string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.string("x").is_number()).to_equal(false)
```

</details>

#### is_string false for non-string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_string()).to_equal(false)
```

</details>

#### is_array false for non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_array()).to_equal(false)
```

</details>

#### is_dict false for non-dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_dict()).to_equal(false)
```

</details>

#### is_table false for non-table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(1).is_table()).to_equal(false)
```

</details>

#### value extraction

#### as_bool returns Some for bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = SdnValue.bool(true).as_bool()
expect(b.?).to_equal(true)
```

</details>

#### as_bool returns nil for non-bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = SdnValue.int(1).as_bool()
expect(b.?).to_equal(false)
```

</details>

#### as_i64 returns Some for int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val i = SdnValue.int(42).as_i64()
expect(i.?).to_equal(true)
```

</details>

#### as_i64 returns nil for non-int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val i = SdnValue.string("x").as_i64()
expect(i.?).to_equal(false)
```

</details>

#### as_f64 returns Some for float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = SdnValue.float(3.14).as_f64()
expect(f.?).to_equal(true)
```

</details>

#### as_f64 returns Some for int (coercion)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = SdnValue.int(42).as_f64()
expect(f.?).to_equal(true)
```

</details>

#### as_f64 returns nil for non-numeric

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = SdnValue.string("x").as_f64()
expect(f.?).to_equal(false)
```

</details>

#### as_str returns Some for string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SdnValue.string("hi").as_str()
expect(s.?).to_equal(true)
```

</details>

#### as_str returns nil for non-string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SdnValue.int(1).as_str()
expect(s.?).to_equal(false)
```

</details>

#### as_array returns Some for array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SdnValue.array([SdnValue.int(1)]).as_array()
expect(a.?).to_equal(true)
```

</details>

#### as_array returns nil for non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SdnValue.int(1).as_array()
expect(a.?).to_equal(false)
```

</details>

#### as_dict returns Some for dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = SdnValue.empty_dict().as_dict()
expect(d.?).to_equal(true)
```

</details>

#### as_dict returns nil for non-dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = SdnValue.int(1).as_dict()
expect(d.?).to_equal(false)
```

</details>

#### mutation

#### insert into dict succeeds

1. var d = SdnValue empty dict
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = SdnValue.empty_dict()
val ok = d.insert("key", SdnValue.string("value"))
expect(ok).to_equal(true)
```

</details>

#### insert into non-dict returns false

1. var v = SdnValue int
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = SdnValue.int(1)
val ok = v.insert("key", SdnValue.string("value"))
expect(ok).to_equal(false)
```

</details>

#### push into array succeeds

1. var arr = SdnValue empty array
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = SdnValue.empty_array()
val ok = arr.push(SdnValue.int(1))
expect(ok).to_equal(true)
```

</details>

#### push into non-array returns false

1. var v = SdnValue int
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = SdnValue.int(1)
val ok = v.push(SdnValue.int(2))
expect(ok).to_equal(false)
```

</details>

#### get and get_path

#### get by key from dict

1. var d = SdnValue empty dict
2. d insert
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = SdnValue.empty_dict()
d.insert("name", SdnValue.string("Alice"))
val result = d.get("name")
expect(result.?).to_equal(true)
```

</details>

#### get returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = SdnValue.empty_dict()
val result = d.get("missing")
expect(result.?).to_equal(false)
```

</details>

#### get returns nil for non-dict non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = SdnValue.int(1)
val result = v.get("x")
expect(result.?).to_equal(false)
```

</details>

#### get by index from array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = SdnValue.array([SdnValue.int(10), SdnValue.int(20)])
val result = arr.get("0")
expect(result.?).to_equal(true)
```

</details>

#### get by out-of-bounds index returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = SdnValue.array([SdnValue.int(10)])
val result = arr.get("5")
expect(result.?).to_equal(false)
```

</details>

#### type_name

#### returns correct type names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.Null.type_name()).to_equal("null")
expect(SdnValue.bool(true).type_name()).to_equal("bool")
expect(SdnValue.int(1).type_name()).to_equal("int")
expect(SdnValue.float(1.0).type_name()).to_equal("float")
expect(SdnValue.string("x").type_name()).to_equal("string")
expect(SdnValue.empty_array().type_name()).to_equal("array")
expect(SdnValue.empty_dict().type_name()).to_equal("dict")
```

</details>

#### to_text display

#### displays null

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.Null.to_text()).to_equal("null")
```

</details>

#### displays true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.bool(true).to_text()).to_equal("true")
```

</details>

#### displays false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.bool(false).to_text()).to_equal("false")
```

</details>

#### displays integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.int(42).to_text()).to_equal("42")
```

</details>

#### displays simple string without quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.string("hello").to_text()).to_equal("hello")
```

</details>

#### displays string with spaces in quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = SdnValue.string("hello world").to_text()
expect(result).to_start_with("\"")
expect(result).to_end_with("\"")
```

</details>

#### displays empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SdnValue.empty_array().to_text()).to_equal("[]")
```

</details>

#### displays array with items

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = SdnValue.array([SdnValue.int(1), SdnValue.int(2)])
val result = arr.to_text()
expect(result).to_equal("[1, 2]")
```

</details>

### SDN Span

#### construction

#### creates empty span

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Span.empty()
expect(s.start).to_equal(0)
expect(s.end).to_equal(0)
expect(s.line).to_equal(0)
expect(s.column).to_equal(0)
```

</details>

#### creates span with values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Span(start: 10, end: 20, line: 1, column: 5)
expect(s.start).to_equal(10)
expect(s.end).to_equal(20)
```

</details>

#### merge

#### merges two spans

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Span(start: 0, end: 5, line: 1, column: 0)
val b = Span(start: 5, end: 10, line: 1, column: 5)
val merged = a.merge(b)
expect(merged.start).to_equal(0)
expect(merged.end).to_equal(10)
```

</details>

### SDN Lexer

#### tokenize

#### tokenizes simple key-value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize("name: Alice")
expect(tokens.len()).to_be_greater_than(0)
```

</details>

#### tokenizes integer value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize("count: 42")
expect(tokens.len()).to_be_greater_than(0)
```

</details>

#### tokenizes boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize("flag: true")
expect(tokens.len()).to_be_greater_than(0)
```

</details>

#### tokenizes empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = tokenize("")
expect(tokens.len()).to_equal(0)
```

</details>

### SDN Parser

#### parse valid input

#### parses simple key-value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("name: Alice")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### parses integer value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("count: 42")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### parses boolean values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("flag: true")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### parses array value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("items: [1, 2, 3]")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### parses multiple key-values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("name: Alice\nage: 30")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### parse_untrusted

#### parses with size limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_untrusted("name: Alice")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### parse_config

#### parses config-style input

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_config("name: Alice")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### parse_safe

#### parses safely

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_safe("name: Alice")
match result:
    case Ok(v):
        expect(v.is_dict()).to_equal(true)
    case Err(e):
        expect("parse failed").to_equal("should not fail")
```

</details>

### SDN Error

#### error constructors

#### creates syntax error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = SdnError.syntax_error("bad token", 1, 5)
expect(err.message()).to_contain("bad token")
```

</details>

#### creates syntax error with span

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span(start: 0, end: 5, line: 1, column: 0)
val err = SdnError.syntax_error_with_span("bad", span)
expect(err.message()).to_contain("bad")
```

</details>

#### creates unexpected token error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span(start: 0, end: 1, line: 1, column: 0)
val err = SdnError.unexpected_token("COLON", "IDENT", span)
expect(err.message()).to_contain("COLON")
```

</details>

#### creates security error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span(start: 0, end: 1, line: 1, column: 0)
val err = SdnError.security_error("blocked", span)
expect(err.is_security_error()).to_equal(true)
```

</details>

#### non-security error returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = SdnError.syntax_error("msg", 1, 1)
expect(err.is_security_error()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 71 |
| Active scenarios | 71 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
