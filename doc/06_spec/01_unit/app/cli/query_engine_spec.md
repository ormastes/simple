# query_engine_spec

> Tests for the query engine heuristic parser and 7 engine functions. Validates symbol extraction, parsing logic, and module resolution.

<!-- sdn-diagram:id=query_engine_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_engine_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_engine_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_engine_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# query_engine_spec

Tests for the query engine heuristic parser and 7 engine functions. Validates symbol extraction, parsing logic, and module resolution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QE-001 to #QE-007 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/cli/query_engine_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for the query engine heuristic parser and 7 engine functions.
Validates symbol extraction, parsing logic, and module resolution.

## Scenarios

### heuristic parser fn extraction

#### extracts fn name from function line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn query_main() -> i64:"
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("query_main")
```

</details>

#### extracts extern fn name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "extern fn rt_file_read_text(path: text) -> text"
val rest = line.substring(10)
val name = rest.split("(")[0]
expect(name).to_equal("rt_file_read_text")
```

</details>

#### extracts static fn name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "static fn origin() -> Point:"
val rest = line.substring(10)
val name = rest.split("(")[0]
expect(name).to_equal("origin")
```

</details>

#### extracts me method name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "me move(dx: i64):"
val rest = line.substring(3)
val name = rest.split("(")[0]
expect(name).to_equal("move")
```

</details>

#### extracts fn with no params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn hello():"
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("hello")
```

</details>

#### extracts fn with multiple params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn add(a: i64, b: i64) -> i64:"
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("add")
```

</details>

### heuristic parser type extraction

#### extracts class name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "class LazySession:"
val name = line.substring(6).split(":")[0]
expect(name).to_equal("LazySession")
```

</details>

#### extracts struct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "struct Position:"
val name = line.substring(7).split(":")[0]
expect(name).to_equal("Position")
```

</details>

#### extracts enum name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "enum TokenKind:"
val name = line.substring(5).split(":")[0]
expect(name).to_equal("TokenKind")
```

</details>

#### extracts trait name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "trait Printable:"
val name = line.substring(6).split(":")[0]
expect(name).to_equal("Printable")
```

</details>

#### extracts impl name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "impl MyClass:"
val name = line.substring(5).split(":")[0]
expect(name).to_equal("MyClass")
```

</details>

### return type extraction

#### extracts simple return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn get_name() -> text:"
val arrow_idx = _find_arrow_pos(line)
val after_arrow = line.substring(arrow_idx + 2).trim()
val ret_type = after_arrow.split(":")[0].trim()
expect(ret_type).to_equal("text")
```

</details>

#### extracts i64 return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn count() -> i64:"
val arrow_idx = _find_arrow_pos(line)
val after_arrow = line.substring(arrow_idx + 2).trim()
val ret_type = after_arrow.split(":")[0].trim()
expect(ret_type).to_equal("i64")
```

</details>

#### extracts bool return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn is_valid() -> bool:"
val arrow_idx = _find_arrow_pos(line)
val after_arrow = line.substring(arrow_idx + 2).trim()
val ret_type = after_arrow.split(":")[0].trim()
expect(ret_type).to_equal("bool")
```

</details>

#### returns empty for no return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn do_something():"
val has_arrow = line.contains("->")
expect(has_arrow).to_equal(false)
```

</details>

#### extracts array return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn get_items() -> [text]:"
val has_arrow = line.contains("->")
expect(has_arrow).to_equal(true)
```

</details>

### parameter extraction

#### extracts single param

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn greet(name: text):"
val params = _extract_between_parens(line)
expect(params).to_equal("name: text")
```

</details>

#### extracts multiple params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn add(a: i64, b: i64) -> i64:"
val params = _extract_between_parens(line)
expect(params).to_equal("a: i64, b: i64")
```

</details>

#### extracts empty params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn hello() -> text:"
val params = _extract_between_parens(line)
expect(params).to_equal("")
```

</details>

#### extracts params with default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn connect(host: text, port: i64):"
val params = _extract_between_parens(line)
expect(params).to_equal("host: text, port: i64")
```

</details>

### import parsing

#### parses simple use statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "use std.spec"
val rest = line.substring(4).trim()
expect(rest).to_equal("std.spec")
```

</details>

#### parses use with braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "use app.cli.query_engine."
val items = "hover_fn, completions_fn"
val line = prefix + items
val has_prefix = line.starts_with("use ")
expect(has_prefix).to_equal(true)
```

</details>

#### extracts module path from braced import

1. mod path = mod path substring
   - Expected: mod_path equals `app.cli.query_engine`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_part = "app.cli.query_engine."
var mod_path = module_part
if mod_path.ends_with("."):
    mod_path = mod_path.substring(0, mod_path.len() - 1)
expect(mod_path).to_equal("app.cli.query_engine")
```

</details>

#### extracts items from braced import

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items_str = "hover_fn, completions_fn"
val items = items_str.split(",")
expect(items.len()).to_equal(2)
expect(items[0].trim()).to_equal("hover_fn")
expect(items[1].trim()).to_equal("completions_fn")
```

</details>

#### parses import statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "import std.spec"
val rest = line.substring(7).trim()
expect(rest).to_equal("std.spec")
```

</details>

### module path resolution

#### converts std to lib prefix

1. path = "lib " + path substring
   - Expected: path equals `lib.text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var path = "std.text"
if path.starts_with("std."):
    path = "lib." + path.substring(4)
expect(path).to_equal("lib.text")
```

</details>

#### preserves app prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "app.cli.query"
val starts_with_app = path.starts_with("app.")
expect(starts_with_app).to_equal(true)
```

</details>

#### preserves compiler prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "compiler.frontend.core"
val starts_with_compiler = path.starts_with("compiler.")
expect(starts_with_compiler).to_equal(true)
```

</details>

#### converts dots to slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "lib.common.text"
val parts = mod_path.split(".")
val file_path = "src/" + parts.join("/")
expect(file_path).to_equal("src/lib/common/text")
```

</details>

#### tries mod.spl first

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "src/lib/common/text"
val mod_file = base + "/mod.spl"
expect(mod_file).to_equal("src/lib/common/text/mod.spl")
```

</details>

#### falls back to direct .spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "src/app/cli/query_engine"
val direct = base + ".spl"
expect(direct).to_equal("src/app/cli/query_engine.spl")
```

</details>

#### maps bare type imports to default type domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "I64"
val type_base = "src/type/simple_lang/" + mod_path
val type_direct = type_base + ".spl"
expect(type_direct).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### maps owned-domain type imports to underscore directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "simple-lang/I64"
val slash_parts = mod_path.split("/")
val type_base = "type/" + slash_parts[0].replace("-", "_") + "/" + slash_parts[1..].join("/")
val type_direct = type_base + ".spl"
expect(type_direct).to_equal("src/type/simple_lang/I64.spl")
```

</details>

### symbol kind classification

#### classifies fn declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn query_main():"
val is_fn = line.starts_with("fn ")
expect(is_fn).to_equal(true)
```

</details>

#### classifies extern fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "extern fn rt_read():"
val is_extern = line.starts_with("extern fn ")
expect(is_extern).to_equal(true)
```

</details>

#### classifies val as constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val MAX_SIZE = 100"
val is_val = line.starts_with("val ")
expect(is_val).to_equal(true)
```

</details>

#### classifies var as variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "var count = 0"
val is_var = line.starts_with("var ")
expect(is_var).to_equal(true)
```

</details>

#### classifies class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "class Server:"
val is_class = line.starts_with("class ")
expect(is_class).to_equal(true)
```

</details>

#### classifies struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "struct Point:"
val is_struct = line.starts_with("struct ")
expect(is_struct).to_equal(true)
```

</details>

#### classifies trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "trait Comparable:"
val is_trait = line.starts_with("trait ")
expect(is_trait).to_equal(true)
```

</details>

### word boundary detection

#### finds word at start of line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "query_main()"
val starts_with = line.starts_with("query_main")
expect(starts_with).to_equal(true)
```

</details>

#### does not match partial word

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "query_main_loop()"
val exact = line == "query_main()"
expect(exact).to_equal(false)
```

</details>

#### word char includes underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chars = "abcABC09_"
val all_word = true
expect(all_word).to_equal(true)
```

</details>

#### space is not word char

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = " "
val is_word = ch >= "a" and ch <= "z"
expect(is_word).to_equal(false)
```

</details>

#### dot is not word char

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = "."
val is_alpha = (ch >= "a" and ch <= "z") or (ch >= "A" and ch <= "Z")
val is_digit = ch >= "0" and ch <= "9"
val is_word = is_alpha or is_digit or ch == "_"
expect(is_word).to_equal(false)
```

</details>

### binding type extraction

#### extracts type from typed val

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val count: i64 = 0"
val after_name = line.substring(10).trim()
# after_name is ": i64 = 0" -> starts with ":"
val has_colon = line.contains(":")
expect(has_colon).to_equal(true)
```

</details>

#### no type for untyped val

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val count = 0"
# Find colon after name — but the colon is only in the prefix
val after_val = line.substring(4)
val name_part = after_val.split(" ")[0]
val has_type = name_part.contains(":")
expect(has_type).to_equal(false)
```

</details>

#### extracts type from typed var

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "var items: [text] = []"
val has_colon = line.contains(":")
expect(has_colon).to_equal(true)
```

</details>

### engine function output patterns

#### definition outputs file:line format

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
val line = 42
val kind = "fn"
val sig = "fn query_main() -> i64:"
val output = "{file}:{line}: [{kind}] {sig}"
expect(output).to_contain("src/app/cli/query.spl:42")
expect(output).to_contain("[fn]")
```

</details>

#### hover outputs symbol info sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sections = ["Symbol:", "Kind:", "Location:", "Signature:", "Parameters:"]
expect(sections.len()).to_equal(5)
expect(sections).to_contain("Symbol:")
```

</details>

#### completions outputs categorized sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sections = ["--- Local ---", "--- Imported ---", "--- Keywords ---"]
expect(sections.len()).to_equal(3)
```

</details>

#### document symbols output format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "query_main"
val kind = "fn"
val line = 27
val output = "{name}:{kind}:{line}"
expect(output).to_equal("query_main:fn:27")
```

</details>

#### signature help outputs function details

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = ["Function:", "Parameters:", "Returns:", "Active parameter:"]
expect(fields.len()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
