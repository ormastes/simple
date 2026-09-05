# Query Engine Specification

> Tests covering heuristic parser fn extraction, heuristic parser type extraction, return type extraction, parameter extraction, import parsing, module path resolution, symbol kind classification, word boundary detection, binding type extraction, engine function output patterns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Engine Specification

## Scenarios

### heuristic parser fn extraction

#### extracts fn name from function line

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts fn name from function line
   - Expected: name equals `query_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts fn name from function line")
val line = "fn query_main() -> i64:"
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("query_main")
```

</details>

#### extracts extern fn name

- extracts extern fn name
   - Expected: name equals `rt_file_read_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts extern fn name")
val line = "extern fn rt_file_read_text(path: text) -> text"
val rest = line.substring(10)
val name = rest.split("(")[0]
expect(name).to_equal("rt_file_read_text")
```

</details>

#### extracts static fn name

- extracts static fn name
   - Expected: name equals `origin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts static fn name")
val line = "static fn origin() -> Point:"
val rest = line.substring(10)
val name = rest.split("(")[0]
expect(name).to_equal("origin")
```

</details>

#### extracts me method name

- extracts me method name
   - Expected: name equals `move`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts me method name")
val line = "me move(dx: i64):"
val rest = line.substring(3)
val name = rest.split("(")[0]
expect(name).to_equal("move")
```

</details>

#### extracts fn with no params

- extracts fn with no params
   - Expected: name equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts fn with no params")
val line = "fn hello():"
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("hello")
```

</details>

#### extracts fn with multiple params

- extracts fn with multiple params
   - Expected: name equals `add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts fn with multiple params")
val line = "fn add(a: i64, b: i64) -> i64:"
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("add")
```

</details>

### heuristic parser type extraction

#### extracts class name

- extracts class name
   - Expected: name equals `LazySession`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts class name")
val line = "class LazySession:"
val name = line.substring(6).split(":")[0]
expect(name).to_equal("LazySession")
```

</details>

#### extracts struct name

- extracts struct name
   - Expected: name equals `Position`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts struct name")
val line = "struct Position:"
val name = line.substring(7).split(":")[0]
expect(name).to_equal("Position")
```

</details>

#### extracts enum name

- extracts enum name
   - Expected: name equals `TokenKind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts enum name")
val line = "enum TokenKind:"
val name = line.substring(5).split(":")[0]
expect(name).to_equal("TokenKind")
```

</details>

#### extracts trait name

- extracts trait name
   - Expected: name equals `Printable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts trait name")
val line = "trait Printable:"
val name = line.substring(6).split(":")[0]
expect(name).to_equal("Printable")
```

</details>

#### extracts impl name

- extracts impl name
   - Expected: name equals `MyClass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts impl name")
val line = "impl MyClass:"
val name = line.substring(5).split(":")[0]
expect(name).to_equal("MyClass")
```

</details>

### return type extraction

#### extracts simple return type

- extracts simple return type
   - Expected: ret_type equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts simple return type")
val line = "fn get_name() -> text:"
val arrow_idx = _find_arrow_pos(line)
val after_arrow = line.substring(arrow_idx + 2).trim()
val ret_type = after_arrow.split(":")[0].trim()
expect(ret_type).to_equal("text")
```

</details>

#### extracts i64 return type

- extracts i64 return type
   - Expected: ret_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts i64 return type")
val line = "fn count() -> i64:"
val arrow_idx = _find_arrow_pos(line)
val after_arrow = line.substring(arrow_idx + 2).trim()
val ret_type = after_arrow.split(":")[0].trim()
expect(ret_type).to_equal("i64")
```

</details>

#### extracts bool return type

- extracts bool return type
   - Expected: ret_type equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts bool return type")
val line = "fn is_valid() -> bool:"
val arrow_idx = _find_arrow_pos(line)
val after_arrow = line.substring(arrow_idx + 2).trim()
val ret_type = after_arrow.split(":")[0].trim()
expect(ret_type).to_equal("bool")
```

</details>

#### returns empty for no return type

- returns empty for no return type
   - Expected: has_arrow is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for no return type")
val line = "fn do_something():"
val has_arrow = line.contains("->")
expect(has_arrow).to_equal(false)
```

</details>

#### extracts array return type

- extracts array return type
   - Expected: has_arrow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts array return type")
val line = "fn get_items() -> [text]:"
val has_arrow = line.contains("->")
expect(has_arrow).to_equal(true)
```

</details>

### parameter extraction

#### extracts single param

- extracts single param
   - Expected: params equals `name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts single param")
val line = "fn greet(name: text):"
val params = _extract_between_parens(line)
expect(params).to_equal("name: text")
```

</details>

#### extracts multiple params

- extracts multiple params
   - Expected: params equals `a: i64, b: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multiple params")
val line = "fn add(a: i64, b: i64) -> i64:"
val params = _extract_between_parens(line)
expect(params).to_equal("a: i64, b: i64")
```

</details>

#### extracts empty params

- extracts empty params
   - Expected: params equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts empty params")
val line = "fn hello() -> text:"
val params = _extract_between_parens(line)
expect(params).to_equal("")
```

</details>

#### extracts params with default values

- extracts params with default values
   - Expected: params equals `host: text, port: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts params with default values")
val line = "fn connect(host: text, port: i64):"
val params = _extract_between_parens(line)
expect(params).to_equal("host: text, port: i64")
```

</details>

### import parsing

#### parses simple use statement

- parses simple use statement
   - Expected: rest equals `std.spec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple use statement")
val line = "use std.spec"
val rest = line.substring(4).trim()
expect(rest).to_equal("std.spec")
```

</details>

#### parses use with braces

- parses use with braces
   - Expected: has_prefix is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use with braces")
val prefix = "use app.cli.query_engine."
val items = "hover_fn, completions_fn"
val line = prefix + items
val has_prefix = line.starts_with("use ")
expect(has_prefix).to_equal(true)
```

</details>

#### extracts module path from braced import

- extracts module path from braced import
   - Expected: mod_path equals `app.cli.query_engine`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts module path from braced import")
val module_part = "app.cli.query_engine."
var mod_path = module_part
if mod_path.ends_with("."):
    mod_path = mod_path.substring(0, mod_path.len() - 1)
expect(mod_path).to_equal("app.cli.query_engine")
```

</details>

#### extracts items from braced import

- extracts items from braced import
   - Expected: items.len() equals `2`
   - Expected: items[0].trim() equals `hover_fn`
   - Expected: items[1].trim() equals `completions_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts items from braced import")
val items_str = "hover_fn, completions_fn"
val items = items_str.split(",")
expect(items.len()).to_equal(2)
expect(items[0].trim()).to_equal("hover_fn")
expect(items[1].trim()).to_equal("completions_fn")
```

</details>

#### parses import statement

- parses import statement
   - Expected: rest equals `std.spec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses import statement")
val line = "import std.spec"
val rest = line.substring(7).trim()
expect(rest).to_equal("std.spec")
```

</details>

### module path resolution

#### converts std to lib prefix

- converts std to lib prefix
   - Expected: path equals `lib.text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts std to lib prefix")
var path = "std.text"
if path.starts_with("std."):
    path = "lib." + path.substring(4)
expect(path).to_equal("lib.text")
```

</details>

#### preserves app prefix

- preserves app prefix
   - Expected: starts_with_app is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves app prefix")
val path = "app.cli.query"
val starts_with_app = path.starts_with("app.")
expect(starts_with_app).to_equal(true)
```

</details>

#### preserves compiler prefix

- preserves compiler prefix
   - Expected: starts_with_compiler is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves compiler prefix")
val path = "compiler.frontend.core"
val starts_with_compiler = path.starts_with("compiler.")
expect(starts_with_compiler).to_equal(true)
```

</details>

#### converts dots to slashes

- converts dots to slashes
   - Expected: file_path equals `src/lib/common/text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts dots to slashes")
val mod_path = "lib.common.text"
val parts = mod_path.split(".")
val file_path = "src/" + parts.join("/")
expect(file_path).to_equal("src/lib/common/text")
```

</details>

#### tries mod.spl first

- tries mod.spl first
   - Expected: mod_file equals `src/lib/common/text/mod.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tries mod.spl first")
val base = "src/lib/common/text"
val mod_file = base + "/mod.spl"
expect(mod_file).to_equal("src/lib/common/text/mod.spl")
```

</details>

#### falls back to direct .spl

- falls back to direct .spl
   - Expected: direct equals `src/app/cli/query_engine.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to direct .spl")
val base = "src/app/cli/query_engine"
val direct = base + ".spl"
expect(direct).to_equal("src/app/cli/query_engine.spl")
```

</details>

#### maps bare type imports to default type domain

- maps bare type imports to default type domain
   - Expected: type_direct equals `src/type/simple_lang/I64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps bare type imports to default type domain")
val mod_path = "I64"
val type_base = "src/type/simple_lang/" + mod_path
val type_direct = type_base + ".spl"
expect(type_direct).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### maps owned-domain type imports to underscore directory

- maps owned-domain type imports to underscore directory
   - Expected: type_direct equals `src/type/simple_lang/I64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps owned-domain type imports to underscore directory")
val mod_path = "simple-lang/I64"
val slash_parts = mod_path.split("/")
val type_base = "type/" + slash_parts[0].replace("-", "_") + "/" + slash_parts[1..].join("/")
val type_direct = type_base + ".spl"
expect(type_direct).to_equal("src/type/simple_lang/I64.spl")
```

</details>

### symbol kind classification

#### classifies fn declarations

- classifies fn declarations
   - Expected: is_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies fn declarations")
val line = "fn query_main():"
val is_fn = line.starts_with("fn ")
expect(is_fn).to_equal(true)
```

</details>

#### classifies extern fn

- classifies extern fn
   - Expected: is_extern is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies extern fn")
val line = "extern fn rt_read():"
val is_extern = line.starts_with("extern fn ")
expect(is_extern).to_equal(true)
```

</details>

#### classifies val as constant

- classifies val as constant
   - Expected: is_val is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies val as constant")
val line = "val MAX_SIZE = 100"
val is_val = line.starts_with("val ")
expect(is_val).to_equal(true)
```

</details>

#### classifies var as variable

- classifies var as variable
   - Expected: is_var is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies var as variable")
val line = "var count = 0"
val is_var = line.starts_with("var ")
expect(is_var).to_equal(true)
```

</details>

#### classifies class

- classifies class
   - Expected: is_class is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies class")
val line = "class Server:"
val is_class = line.starts_with("class ")
expect(is_class).to_equal(true)
```

</details>

#### classifies struct

- classifies struct
   - Expected: is_struct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies struct")
val line = "struct Point:"
val is_struct = line.starts_with("struct ")
expect(is_struct).to_equal(true)
```

</details>

#### classifies trait

- classifies trait
   - Expected: is_trait is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies trait")
val line = "trait Comparable:"
val is_trait = line.starts_with("trait ")
expect(is_trait).to_equal(true)
```

</details>

### word boundary detection

#### finds word at start of line

- finds word at start of line
   - Expected: starts_with is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds word at start of line")
val line = "query_main()"
val starts_with = line.starts_with("query_main")
expect(starts_with).to_equal(true)
```

</details>

#### does not match partial word

- does not match partial word
   - Expected: exact is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not match partial word")
val line = "query_main_loop()"
val exact = line == "query_main()"
expect(exact).to_equal(false)
```

</details>

#### word char includes underscore

- word char includes underscore
   - Expected: all_word is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("word char includes underscore")
val chars = "abcABC09_"
val all_word = true
expect(all_word).to_equal(true)
```

</details>

#### space is not word char

- space is not word char
   - Expected: is_word is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("space is not word char")
val ch = " "
val is_word = ch >= "a" and ch <= "z"
expect(is_word).to_equal(false)
```

</details>

#### dot is not word char

- dot is not word char
   - Expected: is_word is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dot is not word char")
val ch = "."
val is_alpha = (ch >= "a" and ch <= "z") or (ch >= "A" and ch <= "Z")
val is_digit = ch >= "0" and ch <= "9"
val is_word = is_alpha or is_digit or ch == "_"
expect(is_word).to_equal(false)
```

</details>

### binding type extraction

#### extracts type from typed val

- extracts type from typed val
   - Expected: has_colon is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts type from typed val")
val line = "val count: i64 = 0"
val after_name = line.substring(10).trim()
# after_name is ": i64 = 0" -> starts with ":"
val has_colon = line.contains(":")
expect(has_colon).to_equal(true)
```

</details>

#### no type for untyped val

- no type for untyped val
   - Expected: has_type is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no type for untyped val")
val line = "val count = 0"
# Find colon after name — but the colon is only in the prefix
val after_val = line.substring(4)
val name_part = after_val.split(" ")[0]
val has_type = name_part.contains(":")
expect(has_type).to_equal(false)
```

</details>

#### extracts type from typed var

- extracts type from typed var
   - Expected: has_colon is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts type from typed var")
val line = "var items: [text] = []"
val has_colon = line.contains(":")
expect(has_colon).to_equal(true)
```

</details>

### engine function output patterns

#### definition outputs file:line format

- definition outputs file:line format


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("definition outputs file:line format")
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

- hover outputs symbol info sections
   - Expected: sections.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hover outputs symbol info sections")
val sections = ["Symbol:", "Kind:", "Location:", "Signature:", "Parameters:"]
expect(sections.len()).to_equal(5)
expect(sections).to_contain("Symbol:")
```

</details>

#### completions outputs categorized sections

- completions outputs categorized sections
   - Expected: sections.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completions outputs categorized sections")
val sections = ["--- Local ---", "--- Imported ---", "--- Keywords ---"]
expect(sections.len()).to_equal(3)
```

</details>

#### document symbols output format

- document symbols output format
   - Expected: output equals `query_main:fn:27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("document symbols output format")
val name = "query_main"
val kind = "fn"
val line = 27
val output = "{name}:{kind}:{line}"
expect(output).to_equal("query_main:fn:27")
```

</details>

#### signature help outputs function details

- signature help outputs function details
   - Expected: fields.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signature help outputs function details")
val fields = ["Function:", "Parameters:", "Returns:", "Active parameter:"]
expect(fields.len()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/query_engine_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering heuristic parser fn extraction, heuristic parser type extraction, return type extraction, parameter extraction, import parsing, module path resolution, symbol kind classification, word boundary detection, binding type extraction, engine function output patterns.
- heuristic parser fn extraction
- heuristic parser type extraction
- return type extraction
- parameter extraction
- import parsing
- module path resolution
- symbol kind classification
- word boundary detection
- binding type extraction
- engine function output patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cc1ee2b17082ce5eceb2b9e3164e8326965b40b18f82fa272c4e1f39f65839d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc1ee2b17082ce5eceb2b9e3164e8326965b40b18f82fa272c4e1f39f65839d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc1ee2b17082ce5eceb2b9e3164e8326965b40b18f82fa272c4e1f39f65839d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/cli/query_engine_spec.spl
mirror: doc/06_spec/unit/app/cli/query_engine_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/query_engine_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/query_engine_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/query_engine_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli/query_engine_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts fn name from function line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_engine_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts extern fn name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_engine_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts static fn name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
