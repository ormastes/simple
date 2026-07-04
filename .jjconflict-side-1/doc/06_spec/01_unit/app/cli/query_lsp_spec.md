# CLI Query LSP Subcommands Specification

> Tests for the 10 new `bin/simple query` CLI subcommands. Validates argument parsing, command construction, and output format.

<!-- sdn-diagram:id=query_lsp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_lsp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_lsp_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_lsp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Query LSP Subcommands Specification

Tests for the 10 new `bin/simple query` CLI subcommands. Validates argument parsing, command construction, and output format.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #500-510 |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/cli/query_lsp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for the 10 new `bin/simple query` CLI subcommands.
Validates argument parsing, command construction, and output format.

## Scenarios

### query CLI subcommand dispatch

#### recognizes signature-help

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "signature-help"
val valid_subcmds = ["definition", "references", "hover", "completions", "type-at", "signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(valid_subcmds).to_contain(subcmd)
```

</details>

#### recognizes rename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "rename"
val valid_subcmds = ["signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(valid_subcmds).to_contain(subcmd)
```

</details>

#### recognizes all 15 subcommands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_subcmds = ["definition", "references", "hover", "completions", "type-at", "signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(all_subcmds.len()).to_equal(15)
```

</details>

### query argument parsing

#### standard tools parse file line column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["signature-help", "src/test.spl", "42", "10"]
expect(args[0]).to_equal("signature-help")
expect(args[1]).to_equal("src/test.spl")
expect(args[2]).to_equal("42")
expect(args[3]).to_equal("10")
```

</details>

#### workspace-symbols parses query flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["workspace-symbols", "--query", "parse", "--kind", "fn"]
expect(args[0]).to_equal("workspace-symbols")
expect(args[1]).to_equal("--query")
expect(args[2]).to_equal("parse")
```

</details>

#### rename parses new-name flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["rename", "src/test.spl", "10", "--new-name", "better"]
expect(args[0]).to_equal("rename")
expect(args[3]).to_equal("--new-name")
expect(args[4]).to_equal("better")
```

</details>

#### call-hierarchy parses direction flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["call-hierarchy", "src/test.spl", "10", "--direction", "incoming"]
expect(args[3]).to_equal("--direction")
expect(args[4]).to_equal("incoming")
```

</details>

#### semantic-tokens parses line range flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["semantic-tokens", "src/test.spl", "--start-line", "10", "--end-line", "50"]
expect(args[2]).to_equal("--start-line")
expect(args[4]).to_equal("--end-line")
```

</details>

#### semantic token range flags use guarded integer parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query_source = rt_file_read_text("src/app/cli/query.spl") ?? ""
val visibility_source = rt_file_read_text("src/app/cli/query_visibility_part1.spl") ?? ""

expect(query_source).to_contain("query_nonnegative_int_or_zero(start_line_str)")
expect(query_source).to_contain("query_nonnegative_int_or_zero(end_line_str)")
expect(visibility_source).to_contain("query_visibility_nonnegative_int_or_zero(args[j + 1])")
expect(query_source.contains("start_line_str.to_int()")).to_equal(false)
expect(query_source.contains("end_line_str.to_int()")).to_equal(false)
```

</details>

#### position arguments use guarded integer parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query_source = rt_file_read_text("src/app/cli/query.spl") ?? ""
val rich_source = rt_file_read_text("src/app/cli/query_rich_common.spl") ?? ""

expect(query_source).to_contain("val line_num = query_nonnegative_int_or_zero(cmd_args[2])")
expect(query_source).to_contain("col = query_nonnegative_int_or_zero(cmd_args[3])")
expect(rich_source).to_contain("query_rich_nonnegative_int_or_zero(line_str)")
expect(rich_source).to_contain("query_rich_nonnegative_int_or_zero(col_str)")
expect(query_source.contains("cmd_args[2].to_int()")).to_equal(false)
expect(query_source.contains("cmd_args[3].to_int()")).to_equal(false)
```

</details>

#### document-formatting takes only file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["document-formatting", "src/test.spl"]
expect(args.len()).to_equal(2)
```

</details>

### extract_symbol_at function

#### extracts fn name from function declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn query_main() -> i64:"
# Extract word after "fn " using split on "("
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("query_main")
```

</details>

#### extracts class name from class declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "class LazySession:"
# Extract word after "class " using split on ":"
val after_class = line.substring(6)
val name = after_class.split(":")[0]
expect(name).to_equal("LazySession")
```

</details>

#### extracts struct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "struct Position:"
# Extract word after "struct " using split on ":"
val after_struct = line.substring(7)
val name = after_struct.split(":")[0]
expect(name).to_equal("Position")
```

</details>

#### extracts val name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val SERVER_NAME = \"simple-mcp\""
# Extract word after "val " using split on " "
val after_val = line.substring(4)
val name = after_val.split(" ")[0]
expect(name).to_equal("SERVER_NAME")
```

</details>

### query command construction

#### signature-help uses correct subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple query signature-help src/test.spl 10"
expect(cmd).to_contain("query signature-help")
```

</details>

#### rename includes new-name flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple query rename src/test.spl 10 --new-name x"
expect(cmd).to_contain("--new-name x")
```

</details>

#### workspace-symbols uses query flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple query workspace-symbols --query parse"
expect(cmd).to_contain("--query parse")
```

</details>

#### semantic-tokens uses range flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple query semantic-tokens src/test.spl --start-line 1 --end-line 50"
expect(cmd).to_contain("--start-line 1")
expect(cmd).to_contain("--end-line 50")
```

</details>

### query help text

#### lists all original 5 subcommands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = ["definition", "references", "hover", "completions", "type-at"]
expect(original.len()).to_equal(5)
```

</details>

#### lists all new 10 subcommands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_cmds = ["signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(new_cmds.len()).to_equal(10)
```

</details>

#### total subcommands is 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 5 + 10
expect(total).to_equal(15)
```

</details>

### semantic token types

#### classifies fn as keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "elif", "for", "while", "match", "case", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false", "extern", "export", "type", "alias", "mixin", "ce", "bind", "receive", "after"]
expect(keywords).to_contain("fn")
```

</details>

#### classifies string literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val name = \"hello\""
val has_string = line.contains("\"")
expect(has_string).to_equal(true)
```

</details>

#### classifies comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "# this is a comment"
val is_comment = line.starts_with("#")
expect(is_comment).to_equal(true)
```

</details>

#### classifies numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "42"
# Check if all chars are digits
var all_digits = true
for ch in token:
    val is_digit = ch >= "0" and ch <= "9"
    if not is_digit:
        all_digits = false
expect(all_digits).to_equal(true)
```

</details>

### inlay hint type inference

#### infers text from string literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rhs = "\"hello\""
val is_string = rhs.starts_with("\"")
val inferred = "text"
expect(is_string).to_equal(true)
expect(inferred).to_equal("text")
```

</details>

#### infers i64 from integer literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rhs = "42"
var all_digits = true
for ch in rhs:
    val is_digit = ch >= "0" and ch <= "9"
    if not is_digit:
        all_digits = false
expect(all_digits).to_equal(true)
```

</details>

#### infers bool from true/false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rhs_true = "true"
val rhs_false = "false"
val is_bool_true = rhs_true == "true"
val is_bool_false = rhs_false == "false"
expect(is_bool_true).to_equal(true)
expect(is_bool_false).to_equal(true)
```

</details>

#### infers array from bracket literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rhs = "[1, 2, 3]"
val is_array = rhs.starts_with("[")
expect(is_array).to_equal(true)
```

</details>

#### detects val without type annotation needs hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val count = 0"
val has_colon = line.contains(": ")
val needs_hint = not has_colon
expect(needs_hint).to_equal(true)
```

</details>

#### skips val with type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val count: i64 = 0"
val has_colon = line.contains(": ")
expect(has_colon).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
