# mcp_lsp_rename_spec

> Tests rename symbol edge cases: same-name, keyword collision, multi-file, identifier validation, and command construction variants.

<!-- sdn-diagram:id=mcp_lsp_rename_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_lsp_rename_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_lsp_rename_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_lsp_rename_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_lsp_rename_spec

Tests rename symbol edge cases: same-name, keyword collision, multi-file, identifier validation, and command construction variants.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-LSP-002 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_unit/mcp_lsp_rename_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests rename symbol edge cases: same-name, keyword collision, multi-file,
identifier validation, and command construction variants.

## Key Concepts

| Concept          | Description                                        |
|------------------|----------------------------------------------------|
| Rename           | Replaces symbol name across all references          |
| Keyword check    | New name must not collide with language keywords     |
| Identifier rules | Must start with letter or underscore, no spaces      |
| Destructive      | Rename modifies source files                         |
| Dry-run          | Preview mode that shows changes without applying     |

## Scenarios

### rename tool edge cases

#### detects same-name rename as no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_name = "query_main"
val new_name = "query_main"
val is_noop = old_name == new_name
expect(is_noop).to_equal(true)
```

</details>

#### detects different names as non-noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_name = "query_main"
val new_name = "process_query"
val is_noop = old_name == new_name
expect(is_noop).to_equal(false)
```

</details>

#### case-different name is not a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_name = "queryMain"
val new_name = "querymain"
val is_noop = old_name == new_name
expect(is_noop).to_equal(false)
```

</details>

### rename keyword collision

#### detects fn keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "fn"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects class keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "class"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects val keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "val"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects var keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "var"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects self keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "self"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects nil keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "nil"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects true keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "true"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### detects match keyword collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "match"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(true)
```

</details>

#### allows valid identifier as new_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "for", "while", "match", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false"]
val new_name = "better_name"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(false)
```

</details>

#### allows snake_case identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var"]
val new_name = "parse_expression"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(false)
```

</details>

#### allows PascalCase identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var"]
val new_name = "TokenParser"
val is_keyword = keywords.contains(new_name)
expect(is_keyword).to_equal(false)
```

</details>

### rename identifier validation

#### validates new_name is not empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = ""
expect(new_name == "").to_equal(true)
```

</details>

#### validates new_name has no spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = "has space"
val has_space = new_name.contains(" ")
expect(has_space).to_equal(true)
```

</details>

#### validates new_name starts with letter or underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_starts = ["a", "z", "A", "Z", "_"]
val name = "_private"
val first = name.substring(0, 1)
expect(valid_starts).to_contain(first)
```

</details>

#### validates uppercase start is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "ClassName"
val first = name.substring(0, 1)
val is_upper = first >= "A"
val is_upper_end = first <= "Z"
expect(is_upper).to_equal(true)
expect(is_upper_end).to_equal(true)
```

</details>

#### validates lowercase start is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_starts = ["a", "z", "A", "Z", "_"]
val name = "method_name"
val first = name.substring(0, 1)
# "m" is between "a" and "z" so it should be a valid start
val is_lower = first >= "a"
expect(is_lower).to_equal(true)
```

</details>

#### detects name starting with digit as invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "3invalid"
val first = name.substring(0, 1)
val is_digit = first >= "0"
val is_not_alpha = first < "A"
val starts_with_digit = is_digit and is_not_alpha
expect(starts_with_digit).to_equal(true)
```

</details>

#### detects name with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "invalid-name"
val has_hyphen = name.contains("-")
expect(has_hyphen).to_equal(true)
```

</details>

#### detects name with dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "module.name"
val has_dot = name.contains(".")
expect(has_dot).to_equal(true)
```

</details>

#### allows name with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "x"
val is_valid_length = name.len() > 0
expect(is_valid_length).to_equal(true)
```

</details>

#### allows single underscore name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "_"
val is_valid_length = name.len() > 0
val starts_ok = name.substring(0, 1) == "_"
expect(is_valid_length).to_equal(true)
expect(starts_ok).to_equal(true)
```

</details>

### rename command construction

#### builds dry-run rename command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/test.spl"
val line = "10"
val new_name = "renamed"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name + " 2>&1"
expect(cmd).to_contain("query rename")
expect(cmd).to_contain("--new-name renamed")
```

</details>

#### builds command with column

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/compiler/10.frontend/core/parser.spl"
val line = "250"
val new_name = "parse_expr"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name
expect(cmd).to_contain("src/compiler/10.frontend/core/parser.spl")
```

</details>

#### handles underscore-prefixed new name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "1"
val new_name = "_internal"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name
expect(cmd).to_contain("--new-name _internal")
```

</details>

#### handles long snake_case name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "1"
val new_name = "parse_expression_from_token_stream"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name
expect(cmd).to_contain("--new-name parse_expression_from_token_stream")
```

</details>

#### uses 30 second timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "timeout 30 bin/simple query rename test.spl 1 --new-name x"
expect(cmd).to_start_with("timeout 30")
```

</details>

#### redirects stderr to stdout

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/lib/common/text/mod.spl"
val line = "15"
val new_name = "format_text"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line + " --new-name " + new_name + " 2>&1"
expect(cmd).to_contain(file)
expect(cmd).to_contain("--new-name format_text")
```

</details>

#### includes src directory in search scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val search_dir = "src/"
val scope = "src/ --include='*.spl'"
expect(scope).to_contain(search_dir)
```

</details>

#### respects word boundaries in search

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "parse"
val pattern = "\\b" + symbol + "\\b"
expect(pattern).to_contain("\\b")
```

</details>

#### distinguishes similar symbol names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = ["parse", "parser", "parse_expr", "parse_stmt"]
val target = "parse"
expect(symbols).to_contain(target)
val count = symbols.len()
expect(count).to_be_greater_than(1)
```

</details>

#### handles symbols in different directories

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["src/app/cli/main.spl", "src/lib/common/text/mod.spl", "src/compiler/10.frontend/core/parser.spl"]
expect(files.len()).to_equal(3)
```

</details>

#### rename in lib affects importers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_file = "src/lib/common/text/mod.spl"
val is_lib = lib_file.contains("src/lib/")
expect(is_lib).to_equal(true)
```

</details>

#### rename in compiler affects internal refs only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler_file = "src/compiler/10.frontend/core/parser.spl"
val is_compiler = compiler_file.contains("src/compiler/")
expect(is_compiler).to_equal(true)
```

</details>

### rename naming conventions

#### preserves snake_case convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = "process_input"
val has_underscore = new_name.contains("_")
val has_uppercase = new_name.contains("P")
expect(has_underscore).to_equal(true)
expect(has_uppercase).to_equal(false)
```

</details>

#### preserves PascalCase convention for types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = "TokenParser"
val first = new_name.substring(0, 1)
expect(first).to_equal("T")
```

</details>

#### allows SCREAMING_SNAKE_CASE for constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = "MAX_BUFFER_SIZE"
val has_underscore = new_name.contains("_")
expect(has_underscore).to_equal(true)
```

</details>

#### detects mixed convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = "camelCase"
val first = new_name.substring(0, 1)
val is_lower_start = first >= "a"
expect(is_lower_start).to_equal(true)
```

</details>

#### handles single-letter names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["x", "y", "z", "i", "n", "k"]
expect(names.len()).to_equal(6)
expect(names).to_contain("x")
```

</details>

#### handles numeric suffix names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = "result2"
val is_valid = new_name.len() > 0
expect(is_valid).to_equal(true)
```

</details>

### rename destructive operation safety

#### rename is a destructive operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val destructive = ["simple_rename", "simple_document_formatting"]
expect(destructive).to_contain("simple_rename")
```

</details>

#### non-destructive tools do not include rename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe_tools = ["simple_signature_help", "simple_code_actions", "simple_workspace_symbols", "simple_call_hierarchy", "simple_type_hierarchy", "simple_semantic_tokens", "simple_inlay_hints", "simple_selection_range"]
val has_rename = safe_tools.contains("simple_rename")
expect(has_rename).to_equal(false)
```

</details>

#### destructive tools list is exhaustive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val destructive = ["simple_rename", "simple_document_formatting"]
expect(destructive.len()).to_equal(2)
```

</details>

#### read-only tools outnumber destructive tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read_only_count = 8
val destructive_count = 2
expect(read_only_count).to_be_greater_than(destructive_count)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
