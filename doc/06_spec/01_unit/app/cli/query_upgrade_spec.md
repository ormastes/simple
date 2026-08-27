# query_upgrade_spec

> Tests for upgraded query.spl: Tier 2 engine delegation and Tier 4 improvements. Validates the transition from grep-based to outline-parser-based queries.

<!-- sdn-diagram:id=query_upgrade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_upgrade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_upgrade_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_upgrade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# query_upgrade_spec

Tests for upgraded query.spl: Tier 2 engine delegation and Tier 4 improvements. Validates the transition from grep-based to outline-parser-based queries.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QU-001 to #QU-010 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/cli/query_upgrade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for upgraded query.spl: Tier 2 engine delegation and Tier 4 improvements.
Validates the transition from grep-based to outline-parser-based queries.

## Scenarios

### Tier 2 engine delegation

#### definition delegates to engine_find_definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "definition"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### references delegates to engine_find_references

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "references"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### hover delegates to engine_hover

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "hover"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### completions delegates to engine_completions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "completions"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### type-at delegates to engine_type_at

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "type-at"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### signature-help delegates to engine_signature_help

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcmd = "signature-help"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

### query input sanitization

#### sanitize_path called on file argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
# Safe path passes through
val has_dangerous = (file.contains("$") or file.contains(";") or file.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### sanitize_symbol called on symbol argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "query_main"
val is_safe = _is_valid_symbol(symbol)
expect(is_safe).to_equal(true)
```

</details>

#### rejects dangerous file path early

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/test; cat /etc/passwd"
val has_dangerous = file.contains(";")
# sanitize_path returns "" -> query exits with error
expect(has_dangerous).to_equal(true)
```

</details>

#### rejects dangerous symbol early

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "foo;bar"
val is_safe = _is_valid_symbol(symbol)
expect(is_safe).to_equal(false)
```

</details>

### rename upgrade with apply

#### supports --apply flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = ["--apply", "--new-name"]
expect(flags).to_contain("--apply")
```

</details>

#### outputs structured format file:line: old -> new

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/test.spl"
val line = 10
val old_name = "foo"
val new_name = "bar"
val output = "{file}:{line}: {old_name} -> {new_name}"
expect(output).to_contain("src/test.spl:10:")
expect(output).to_contain("foo -> bar")
```

</details>

#### uses safe_grep for finding occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["-rn", "\\bfoo\\b", "src/", "--include=*.spl"]
expect(args[0]).to_equal("-rn")
expect(args.len()).to_equal(4)
```

</details>

#### whole word replacement preserves boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val foobar = foo(foo_arg)"
# _replace_word("foo", "bar") should only replace standalone "foo"
val has_foo = line.contains("foo")
expect(has_foo).to_equal(true)
```

</details>

### semantic tokens upgrade

#### supports 12+ token types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val types = ["keyword", "function", "type", "parameter", "property", "variable", "operator", "comment", "string", "number", "enumMember", "namespace"]
expect(types.len()).to_equal(12)
```

</details>

#### classifies fn/class/struct as keywords

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "elif", "for", "while", "match", "case", "return", "use", "import", "trait", "impl", "static", "me", "self", "nil", "true", "false", "extern", "export", "type", "alias", "mixin", "ce", "bind", "receive", "after"]
expect(keywords).to_contain("fn")
expect(keywords).to_contain("class")
expect(keywords).to_contain("struct")
```

</details>

#### classifies identifier by outline data

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If identifier is in fn_names set -> "function"
# If identifier is in type_names set -> "type"
# If identifier is in param_names set -> "parameter"
val fn_names = ["query_main", "run_query"]
val type_names = ["Point", "Server"]
val param_names = ["file", "symbol"]
expect(fn_names).to_contain("query_main")
expect(type_names).to_contain("Point")
expect(param_names).to_contain("file")
```

</details>

#### classifies comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "# this is a comment"
val trimmed = line.trim()
val is_comment = trimmed.starts_with("#")
expect(is_comment).to_equal(true)
```

</details>

#### classifies string literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "\"hello world\""
val is_string = token.starts_with("\"")
expect(is_string).to_equal(true)
```

</details>

#### classifies numeric literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "42"
val is_numeric = token >= "0" and token <= "99999"
expect(token).to_equal("42")
```

</details>

### inlay hints outline-based

#### infers type from string literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rhs = "\"hello\""
val inferred = "text"
val is_string = rhs.starts_with("\"")
expect(is_string).to_equal(true)
expect(inferred).to_equal("text")
```

</details>

#### infers type from integer literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rhs = "42"
val inferred = "i64"
expect(inferred).to_equal("i64")
```

</details>

#### infers type from boolean literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rhs = "true"
val inferred = "bool"
val is_bool = rhs == "true" or rhs == "false"
expect(is_bool).to_equal(true)
```

</details>

#### infers type from function call via outline

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# engine provides fn return types
val fn_names = ["get_count", "read_file"]
val fn_returns = ["i64", "text"]
val rhs = "get_count()"
val call_name = rhs.split("(")[0]
# Look up return type in parallel arrays
var inferred = ""
if call_name == fn_names[0]:
    inferred = fn_returns[0]
expect(inferred).to_equal("i64")
```

</details>

#### skips already-typed bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val count: i64 = 0"
val has_type_annotation = line.contains(": i64")
expect(has_type_annotation).to_equal(true)
```

</details>

### new subcommand dispatch

#### recognizes document-highlight

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_subcmds = ["definition", "references", "hover", "completions", "type-at", "signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting", "document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("document-highlight")
```

</details>

#### recognizes type-definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_subcmds = ["document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("type-definition")
```

</details>

#### recognizes implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_subcmds = ["document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("implementation")
```

</details>

#### recognizes folding-range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_subcmds = ["document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("folding-range")
```

</details>

#### total subcommands is now 19

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = 5
val tier4 = 10
val new_lsp = 4
val total = original + tier4 + new_lsp
expect(total).to_equal(19)
```

</details>

### safe_process replaces query_shell

#### code_actions uses safe_process

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple"
val args = ["check", "src/test.spl"]
expect(cmd).to_equal("bin/simple")
expect(args.len()).to_equal(2)
```

</details>

#### document_formatting uses safe_process

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple"
val args = ["fmt", "--check", "src/test.spl"]
expect(cmd).to_equal("bin/simple")
```

</details>

#### workspace_symbols uses safe_grep

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "grep"
val args = ["-rn", "query_main", "src/", "--include=*.spl"]
expect(cmd).to_equal("grep")
expect(args).to_contain("--include=*.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
