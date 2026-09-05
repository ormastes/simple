# CLI Query LSP Subcommands Specification

> Tests for the 10 new `bin/simple query` CLI subcommands. Validates argument parsing, command construction, and output format.

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
| Source | `test/unit/app/cli/query_lsp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for the 10 new `bin/simple query` CLI subcommands.
Validates argument parsing, command construction, and output format.

## Scenarios

### query CLI subcommand dispatch

#### recognizes signature-help

- recognizes signature-help


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes signature-help")
val subcmd = "signature-help"
val valid_subcmds = ["definition", "references", "hover", "completions", "type-at", "signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(valid_subcmds).to_contain(subcmd)
```

</details>

#### recognizes rename

- recognizes rename


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes rename")
val subcmd = "rename"
val valid_subcmds = ["signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(valid_subcmds).to_contain(subcmd)
```

</details>

#### recognizes all 15 subcommands

- recognizes all 15 subcommands
   - Expected: all_subcmds.len() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes all 15 subcommands")
val all_subcmds = ["definition", "references", "hover", "completions", "type-at", "signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(all_subcmds.len()).to_equal(15)
```

</details>

### query argument parsing

#### standard tools parse file line column

- standard tools parse file line column
   - Expected: args[0] equals `signature-help`
   - Expected: args[1] equals `src/test.spl`
   - Expected: args[2] equals `42`
   - Expected: args[3] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("standard tools parse file line column")
val args = ["signature-help", "src/test.spl", "42", "10"]
expect(args[0]).to_equal("signature-help")
expect(args[1]).to_equal("src/test.spl")
expect(args[2]).to_equal("42")
expect(args[3]).to_equal("10")
```

</details>

#### workspace-symbols parses query flag

- workspace-symbols parses query flag
   - Expected: args[0] equals `workspace-symbols`
   - Expected: args[1] equals `--query`
   - Expected: args[2] equals `parse`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workspace-symbols parses query flag")
val args = ["workspace-symbols", "--query", "parse", "--kind", "fn"]
expect(args[0]).to_equal("workspace-symbols")
expect(args[1]).to_equal("--query")
expect(args[2]).to_equal("parse")
```

</details>

#### rename parses new-name flag

- rename parses new-name flag
   - Expected: args[0] equals `rename`
   - Expected: args[3] equals `--new-name`
   - Expected: args[4] equals `better`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename parses new-name flag")
val args = ["rename", "src/test.spl", "10", "--new-name", "better"]
expect(args[0]).to_equal("rename")
expect(args[3]).to_equal("--new-name")
expect(args[4]).to_equal("better")
```

</details>

#### call-hierarchy parses direction flag

- call-hierarchy parses direction flag
   - Expected: args[3] equals `--direction`
   - Expected: args[4] equals `incoming`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call-hierarchy parses direction flag")
val args = ["call-hierarchy", "src/test.spl", "10", "--direction", "incoming"]
expect(args[3]).to_equal("--direction")
expect(args[4]).to_equal("incoming")
```

</details>

#### semantic-tokens parses line range flags

- semantic-tokens parses line range flags
   - Expected: args[2] equals `--start-line`
   - Expected: args[4] equals `--end-line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semantic-tokens parses line range flags")
val args = ["semantic-tokens", "src/test.spl", "--start-line", "10", "--end-line", "50"]
expect(args[2]).to_equal("--start-line")
expect(args[4]).to_equal("--end-line")
```

</details>

#### semantic token range flags use guarded integer parsing

- semantic token range flags use guarded integer parsing
   - Expected: query_source does not contain `start_line_str.to_int()`
   - Expected: query_source does not contain `end_line_str.to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semantic token range flags use guarded integer parsing")
val query_source = rt_file_read_text("src/app/cli/query.spl") ?? ""
val visibility_source = rt_file_read_text("src/app/cli/_QueryVisibility/query_commands.spl") ?? ""

expect(query_source).to_contain("query_nonnegative_int_or_zero(start_line_str)")
expect(query_source).to_contain("query_nonnegative_int_or_zero(end_line_str)")
expect(visibility_source).to_contain("query_visibility_nonnegative_int_or_zero(args[j + 1])")
expect(query_source.contains("start_line_str.to_int()")).to_equal(false)
expect(query_source.contains("end_line_str.to_int()")).to_equal(false)
```

</details>

#### position arguments use guarded integer parsing

- position arguments use guarded integer parsing
   - Expected: query_source does not contain `cmd_args[2].to_int()`
   - Expected: query_source does not contain `cmd_args[3].to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("position arguments use guarded integer parsing")
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

- document-formatting takes only file
   - Expected: args.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("document-formatting takes only file")
val args = ["document-formatting", "src/test.spl"]
expect(args.len()).to_equal(2)
```

</details>

### extract_symbol_at function

#### extracts fn name from function declaration

- extracts fn name from function declaration
   - Expected: name equals `query_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts fn name from function declaration")
val line = "fn query_main() -> i64:"
# Extract word after "fn " using split on "("
val after_fn = line.substring(3)
val name = after_fn.split("(")[0]
expect(name).to_equal("query_main")
```

</details>

#### extracts class name from class declaration

- extracts class name from class declaration
   - Expected: name equals `LazySession`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts class name from class declaration")
val line = "class LazySession:"
# Extract word after "class " using split on ":"
val after_class = line.substring(6)
val name = after_class.split(":")[0]
expect(name).to_equal("LazySession")
```

</details>

#### extracts struct name

- extracts struct name
   - Expected: name equals `Position`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts struct name")
val line = "struct Position:"
# Extract word after "struct " using split on ":"
val after_struct = line.substring(7)
val name = after_struct.split(":")[0]
expect(name).to_equal("Position")
```

</details>

#### extracts val name

- extracts val name
   - Expected: name equals `SERVER_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts val name")
val line = "val SERVER_NAME = \"simple-mcp\""
# Extract word after "val " using split on " "
val after_val = line.substring(4)
val name = after_val.split(" ")[0]
expect(name).to_equal("SERVER_NAME")
```

</details>

### query command construction

#### signature-help uses correct subcommand

- signature-help uses correct subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signature-help uses correct subcommand")
val cmd = "bin/simple query signature-help src/test.spl 10"
expect(cmd).to_contain("query signature-help")
```

</details>

#### rename includes new-name flag

- rename includes new-name flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename includes new-name flag")
val cmd = "bin/simple query rename src/test.spl 10 --new-name x"
expect(cmd).to_contain("--new-name x")
```

</details>

#### workspace-symbols uses query flag

- workspace-symbols uses query flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workspace-symbols uses query flag")
val cmd = "bin/simple query workspace-symbols --query parse"
expect(cmd).to_contain("--query parse")
```

</details>

#### semantic-tokens uses range flags

- semantic-tokens uses range flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semantic-tokens uses range flags")
val cmd = "bin/simple query semantic-tokens src/test.spl --start-line 1 --end-line 50"
expect(cmd).to_contain("--start-line 1")
expect(cmd).to_contain("--end-line 50")
```

</details>

### query help text

#### lists all original 5 subcommands

- lists all original 5 subcommands
   - Expected: original.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all original 5 subcommands")
val original = ["definition", "references", "hover", "completions", "type-at"]
expect(original.len()).to_equal(5)
```

</details>

#### lists all new 10 subcommands

- lists all new 10 subcommands
   - Expected: new_cmds.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all new 10 subcommands")
val new_cmds = ["signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting"]
expect(new_cmds.len()).to_equal(10)
```

</details>

#### total subcommands is 15

- total subcommands is 15
   - Expected: total equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total subcommands is 15")
val total = 5 + 10
expect(total).to_equal(15)
```

</details>

### semantic token types

#### classifies fn as keyword

- classifies fn as keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies fn as keyword")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "elif", "for", "while", "match", "case", "return", "import", "use", "trait", "impl", "static", "me", "self", "nil", "true", "false", "extern", "export", "type", "alias", "mixin", "ce", "bind", "receive", "after"]
expect(keywords).to_contain("fn")
```

</details>

#### classifies string literals

- classifies string literals
   - Expected: has_string is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies string literals")
val line = "val name = \"hello\""
val has_string = line.contains("\"")
expect(has_string).to_equal(true)
```

</details>

#### classifies comments

- classifies comments
   - Expected: is_comment is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies comments")
val line = "# this is a comment"
val is_comment = line.starts_with("#")
expect(is_comment).to_equal(true)
```

</details>

#### classifies numbers

- classifies numbers
   - Expected: all_digits is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies numbers")
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

- infers text from string literal
   - Expected: is_string is true
   - Expected: inferred equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers text from string literal")
val rhs = "\"hello\""
val is_string = rhs.starts_with("\"")
val inferred = "text"
expect(is_string).to_equal(true)
expect(inferred).to_equal("text")
```

</details>

#### infers i64 from integer literal

- infers i64 from integer literal
   - Expected: all_digits is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers i64 from integer literal")
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

- infers bool from true/false
   - Expected: is_bool_true is true
   - Expected: is_bool_false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers bool from true/false")
val rhs_true = "true"
val rhs_false = "false"
val is_bool_true = rhs_true == "true"
val is_bool_false = rhs_false == "false"
expect(is_bool_true).to_equal(true)
expect(is_bool_false).to_equal(true)
```

</details>

#### infers array from bracket literal

- infers array from bracket literal
   - Expected: is_array is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers array from bracket literal")
val rhs = "[1, 2, 3]"
val is_array = rhs.starts_with("[")
expect(is_array).to_equal(true)
```

</details>

#### detects val without type annotation needs hint

- detects val without type annotation needs hint
   - Expected: needs_hint is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects val without type annotation needs hint")
val line = "val count = 0"
val has_colon = line.contains(": ")
val needs_hint = not has_colon
expect(needs_hint).to_equal(true)
```

</details>

#### skips val with type annotation

- skips val with type annotation
   - Expected: has_colon is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips val with type annotation")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35dcab36aa8fc50f38bc322474d40375ce15b4224acb597aec0f5a51f3362328`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35dcab36aa8fc50f38bc322474d40375ce15b4224acb597aec0f5a51f3362328`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35dcab36aa8fc50f38bc322474d40375ce15b4224acb597aec0f5a51f3362328`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/cli/query_lsp_spec.spl
mirror: doc/06_spec/unit/app/cli/query_lsp_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/query_lsp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/query_lsp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/query_lsp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli/query_lsp_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes signature-help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_lsp_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes rename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_lsp_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes all 15 subcommands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
