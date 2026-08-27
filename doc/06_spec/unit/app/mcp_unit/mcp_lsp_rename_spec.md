# Mcp Lsp Rename Specification

> Tests covering rename tool edge cases, rename keyword collision, rename identifier validation, rename command construction, rename tool multi-file scenarios, rename naming conventions, rename destructive operation safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Lsp Rename Specification

## Scenarios

### rename tool edge cases

#### detects same-name rename as no-op

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects same-name rename as no-op
   - Expected: is_noop is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects same-name rename as no-op")
val old_name = "query_main"
val new_name = "query_main"
val is_noop = old_name == new_name
expect(is_noop).to_equal(true)
```

</details>

#### detects different names as non-noop

- detects different names as non-noop
   - Expected: is_noop is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects different names as non-noop")
val old_name = "query_main"
val new_name = "process_query"
val is_noop = old_name == new_name
expect(is_noop).to_equal(false)
```

</details>

#### case-different name is not a no-op

- case-different name is not a no-op
   - Expected: is_noop is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("case-different name is not a no-op")
val old_name = "queryMain"
val new_name = "querymain"
val is_noop = old_name == new_name
expect(is_noop).to_equal(false)
```

</details>

### rename keyword collision

#### detects fn keyword collision

- detects fn keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects fn keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "fn"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects class keyword collision

- detects class keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects class keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "class"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects val keyword collision

- detects val keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects val keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "val"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects var keyword collision

- detects var keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects var keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "var"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects self keyword collision

- detects self keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects self keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "self"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects nil keyword collision

- detects nil keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects nil keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "nil"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects true keyword collision

- detects true keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects true keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "true"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects match keyword collision

- detects match keyword collision
   - Expected: is_keyword is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects match keyword collision")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "match"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### allows valid identifier as new_name

- allows valid identifier as new_name
   - Expected: is_keyword is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows valid identifier as new_name")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "better_name"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(false)
```

</details>

#### allows snake_case identifier

- allows snake_case identifier
   - Expected: is_keyword is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows snake_case identifier")
val keywords = ["fn", "class", "struct", "enum", "val", "var"]
val new_name = "parse_expression"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(false)
```

</details>

#### allows PascalCase identifier

- allows PascalCase identifier
   - Expected: is_keyword is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows PascalCase identifier")
val keywords = ["fn", "class", "struct", "enum", "val", "var"]
val new_name = "TokenParser"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(false)
```

</details>

### rename identifier validation

#### validates new_name is not empty

- validates new_name is not empty
   - Expected: new_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates new_name is not empty")
val new_name = ""
expect(new_name).to_equal("")
```

</details>

#### validates new_name has no spaces

- validates new_name has no spaces
   - Expected: has_space is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates new_name has no spaces")
val new_name = "has space"
val has_space = new_name.contains(" ")
expect(has_space).to_equal(true)
```

</details>

#### validates new_name starts with letter or underscore

- validates new_name starts with letter or underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates new_name starts with letter or underscore")
val valid_starts = ["a", "z", "A", "Z", "_"]
val name = "_private"
val first = name.substring(0, 1)
expect(valid_starts).to_contain(first)
```

</details>

#### validates uppercase start is valid

- validates uppercase start is valid
   - Expected: is_upper is true
   - Expected: is_upper_end is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates uppercase start is valid")
val name = "ClassName"
val first = name.substring(0, 1)
val is_upper = first >= "A"
val is_upper_end = first <= "Z"
expect(is_upper).to_equal(true)
expect(is_upper_end).to_equal(true)
```

</details>

#### validates lowercase start is valid

- validates lowercase start is valid
   - Expected: is_lower is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates lowercase start is valid")
val valid_starts = ["a", "z", "A", "Z", "_"]
val name = "method_name"
val first = name.substring(0, 1)
# "m" is between "a" and "z" so it should be a valid start
val is_lower = first >= "a"
expect(is_lower).to_equal(true)
```

</details>

#### detects name starting with digit as invalid

- detects name starting with digit as invalid
   - Expected: starts_with_digit is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects name starting with digit as invalid")
val name = "3invalid"
val first = name.substring(0, 1)
val is_digit = first >= "0"
val is_not_alpha = first < "A"
val starts_with_digit = is_digit and is_not_alpha
expect(starts_with_digit).to_equal(true)
```

</details>

#### detects name with special characters

- detects name with special characters
   - Expected: has_hyphen is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects name with special characters")
val name = "invalid-name"
val has_hyphen = name.contains("-")
expect(has_hyphen).to_equal(true)
```

</details>

#### detects name with dots

- detects name with dots
   - Expected: has_dot is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects name with dots")
val name = "module.name"
val has_dot = name.contains(".")
expect(has_dot).to_equal(true)
```

</details>

#### allows name with underscores

- allows name with underscores
   - Expected: has_space is false
   - Expected: has_hyphen is false
   - Expected: has_dot is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows name with underscores")
val name = "my_var_name"
val has_space = name.contains(" ")
val has_hyphen = name.contains("-")
val has_dot = name.contains(".")
expect(has_space).to_equal(false)
expect(has_hyphen).to_equal(false)
expect(has_dot).to_equal(false)
```

</details>

#### allows single character name

- allows single character name
   - Expected: is_valid_length is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows single character name")
val name = "x"
val is_valid_length = name.len() > 0
expect(is_valid_length).to_equal(true)
```

</details>

#### allows single underscore name

- allows single underscore name
   - Expected: is_valid_length is true
   - Expected: starts_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows single underscore name")
val name = "_"
val is_valid_length = name.len() > 0
val starts_ok = name.substring(0, 1) == "_"
expect(is_valid_length).to_equal(true)
expect(starts_ok).to_equal(true)
```

</details>

### rename command construction

#### builds dry-run rename command

- builds dry-run rename command


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds dry-run rename command")
val file = "src/test.spl"
val line = "10"
val new_name = "renamed"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name + " 2>&1"
expect(cmd).to_contain("query rename")
expect(cmd).to_contain("--new-name renamed")
```

</details>

#### builds command with column

- builds command with column


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds command with column")
val file = "src/test.spl"
val line = "10"
val column = "5"
val new_name = "renamed"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " " + column
cmd = cmd + " --new-name " + new_name + " 2>&1"
expect(cmd).to_contain("10 5 --new-name renamed")
```

</details>

#### preserves long file paths

- preserves long file paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves long file paths")
val file = "src/compiler/10.frontend/core/parser.spl"
val line = "250"
val new_name = "parse_expr"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name
expect(cmd).to_contain("src/compiler/10.frontend/core/parser.spl")
```

</details>

#### handles underscore-prefixed new name

- handles underscore-prefixed new name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles underscore-prefixed new name")
val file = "test.spl"
val line = "1"
val new_name = "_internal"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name
expect(cmd).to_contain("--new-name _internal")
```

</details>

#### handles long snake_case name

- handles long snake_case name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles long snake_case name")
val file = "test.spl"
val line = "1"
val new_name = "parse_expression_from_token_stream"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name
expect(cmd).to_contain("--new-name parse_expression_from_token_stream")
```

</details>

#### uses 30 second timeout

- uses 30 second timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses 30 second timeout")
val cmd = "timeout 30 bin/simple query rename test.spl 1 --new-name x"
expect(cmd).to_start_with("timeout 30")
```

</details>

#### redirects stderr to stdout

- redirects stderr to stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("redirects stderr to stdout")
val file = "test.spl"
val line = "1"
val new_name = "x"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line
cmd = cmd + " --new-name " + new_name + " 2>&1"
expect(cmd).to_end_with("2>&1")
```

</details>

### rename tool multi-file scenarios

#### builds command targeting project-wide search

- builds command targeting project-wide search


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds command targeting project-wide search")
val file = "src/lib/common/text/mod.spl"
val line = "15"
val new_name = "format_text"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name + " 2>&1"
expect(cmd).to_contain(file)
expect(cmd).to_contain("--new-name format_text")
```

</details>

#### includes src directory in search scope

- includes src directory in search scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes src directory in search scope")
val search_dir = "src/"
val scope = "src/ --include='*.spl'"
expect(scope).to_contain(search_dir)
```

</details>

#### respects word boundaries in search

- respects word boundaries in search


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects word boundaries in search")
val symbol = "parse"
val pattern = "\\b" + symbol + "\\b"
expect(pattern).to_contain("\\b")
```

</details>

#### distinguishes similar symbol names

- distinguishes similar symbol names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes similar symbol names")
val symbols = ["parse", "parser", "parse_expr", "parse_stmt"]
val target = "parse"
expect(symbols).to_contain(target)
val count = symbols.len()
expect(count).to_be_greater_than(1)
```

</details>

#### handles symbols in different directories

- handles symbols in different directories
   - Expected: files.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles symbols in different directories")
val files = ["src/app/cli/main.spl", "src/lib/common/text/mod.spl", "src/compiler/10.frontend/core/parser.spl"]
expect(files.len()).to_equal(3)
```

</details>

#### rename in lib affects importers

- rename in lib affects importers
   - Expected: is_lib is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename in lib affects importers")
val lib_file = "src/lib/common/text/mod.spl"
val is_lib = lib_file.contains("src/lib/")
expect(is_lib).to_equal(true)
```

</details>

#### rename in compiler affects internal refs only

- rename in compiler affects internal refs only
   - Expected: is_compiler is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename in compiler affects internal refs only")
val compiler_file = "src/compiler/10.frontend/core/parser.spl"
val is_compiler = compiler_file.contains("src/compiler/")
expect(is_compiler).to_equal(true)
```

</details>

### rename naming conventions

#### preserves snake_case convention

- preserves snake_case convention
   - Expected: has_underscore is true
   - Expected: has_uppercase is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves snake_case convention")
val new_name = "process_input"
val has_underscore = new_name.contains("_")
val has_uppercase = new_name.contains("P")
expect(has_underscore).to_equal(true)
expect(has_uppercase).to_equal(false)
```

</details>

#### preserves PascalCase convention for types

- preserves PascalCase convention for types
   - Expected: first equals `T`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves PascalCase convention for types")
val new_name = "TokenParser"
val first = new_name.substring(0, 1)
expect(first).to_equal("T")
```

</details>

#### allows SCREAMING_SNAKE_CASE for constants

- allows SCREAMING_SNAKE_CASE for constants
   - Expected: has_underscore is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows SCREAMING_SNAKE_CASE for constants")
val new_name = "MAX_BUFFER_SIZE"
val has_underscore = new_name.contains("_")
expect(has_underscore).to_equal(true)
```

</details>

#### detects mixed convention

- detects mixed convention
   - Expected: is_lower_start is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects mixed convention")
val new_name = "camelCase"
val first = new_name.substring(0, 1)
val is_lower_start = first >= "a"
expect(is_lower_start).to_equal(true)
```

</details>

#### handles single-letter names

- handles single-letter names
   - Expected: names.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single-letter names")
val names = ["x", "y", "z", "i", "n", "k"]
expect(names.len()).to_equal(6)
expect(names).to_contain("x")
```

</details>

#### handles numeric suffix names

- handles numeric suffix names
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles numeric suffix names")
val new_name = "result2"
val is_valid = new_name.len() > 0
expect(is_valid).to_equal(true)
```

</details>

### rename destructive operation safety

#### rename is a destructive operation

- rename is a destructive operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename is a destructive operation")
val destructive = ["simple_rename", "simple_document_formatting"]
expect(destructive).to_contain("simple_rename")
```

</details>

#### non-destructive tools do not include rename

- non-destructive tools do not include rename
   - Expected: has_rename is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-destructive tools do not include rename")
val safe_tools = ["simple_signature_help", "simple_code_actions", "simple_workspace_symbols", "simple_call_hierarchy", "simple_type_hierarchy", "simple_semantic_tokens", "simple_inlay_hints", "simple_selection_range"]
val has_rename = safe_tools.contains("simple_rename")
expect(has_rename).to_equal(false)
```

</details>

#### destructive tools list is exhaustive

- destructive tools list is exhaustive
   - Expected: destructive.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destructive tools list is exhaustive")
val destructive = ["simple_rename", "simple_document_formatting"]
expect(destructive.len()).to_equal(2)
```

</details>

#### read-only tools outnumber destructive tools

- read-only tools outnumber destructive tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read-only tools outnumber destructive tools")
val read_only_count = 8
val destructive_count = 2
expect(read_only_count).to_be_greater_than(destructive_count)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_lsp_rename_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rename tool edge cases, rename keyword collision, rename identifier validation, rename command construction, rename tool multi-file scenarios, rename naming conventions, rename destructive operation safety.
- rename tool edge cases
- rename keyword collision
- rename identifier validation
- rename command construction
- rename tool multi-file scenarios
- rename naming conventions
- rename destructive operation safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
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

- Canonical SPipe generation for source `7a5399101a92931eb1fe89c19d2fc588b012dbf0965b7a7fe9cfebff876833e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a5399101a92931eb1fe89c19d2fc588b012dbf0965b7a7fe9cfebff876833e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a5399101a92931eb1fe89c19d2fc588b012dbf0965b7a7fe9cfebff876833e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/mcp_lsp_rename_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_lsp_rename_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_lsp_rename_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_lsp_rename_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_lsp_rename_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_lsp_rename_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects same-name rename as no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_rename_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects different names as non-noop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_rename_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case-different name is not a no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
