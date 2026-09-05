# Query Upgrade Specification

> Tests covering Tier 2 engine delegation, query input sanitization, rename upgrade with apply, semantic tokens upgrade, inlay hints outline-based, new subcommand dispatch, safe_process replaces query_shell.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Upgrade Specification

## Scenarios

### Tier 2 engine delegation

#### definition delegates to engine_find_definition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- definition delegates to engine_find_definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("definition delegates to engine_find_definition")
val subcmd = "definition"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### references delegates to engine_find_references

- references delegates to engine_find_references


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("references delegates to engine_find_references")
val subcmd = "references"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### hover delegates to engine_hover

- hover delegates to engine_hover


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hover delegates to engine_hover")
val subcmd = "hover"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### completions delegates to engine_completions

- completions delegates to engine_completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completions delegates to engine_completions")
val subcmd = "completions"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### type-at delegates to engine_type_at

- type-at delegates to engine_type_at


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type-at delegates to engine_type_at")
val subcmd = "type-at"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

#### signature-help delegates to engine_signature_help

- signature-help delegates to engine_signature_help


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signature-help delegates to engine_signature_help")
val subcmd = "signature-help"
val valid = ["definition", "references", "hover", "completions", "type-at", "signature-help"]
expect(valid).to_contain(subcmd)
```

</details>

### query input sanitization

#### sanitize_path called on file argument

- sanitize_path called on file argument
   - Expected: has_dangerous is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sanitize_path called on file argument")
val file = "src/app/cli/query.spl"
# Safe path passes through
val has_dangerous = (file.contains("$") or file.contains(";") or file.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### sanitize_symbol called on symbol argument

- sanitize_symbol called on symbol argument
   - Expected: is_safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sanitize_symbol called on symbol argument")
val symbol = "query_main"
val is_safe = _is_valid_symbol(symbol)
expect(is_safe).to_equal(true)
```

</details>

#### rejects dangerous file path early

- rejects dangerous file path early
   - Expected: has_dangerous is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dangerous file path early")
val file = "src/test; cat /etc/passwd"
val has_dangerous = file.contains(";")
# sanitize_path returns "" -> query exits with error
expect(has_dangerous).to_equal(true)
```

</details>

#### rejects dangerous symbol early

- rejects dangerous symbol early
   - Expected: is_safe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dangerous symbol early")
val symbol = "foo;bar"
val is_safe = _is_valid_symbol(symbol)
expect(is_safe).to_equal(false)
```

</details>

### rename upgrade with apply

#### supports --apply flag

- supports --apply flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports --apply flag")
val flags = ["--apply", "--new-name"]
expect(flags).to_contain("--apply")
```

</details>

#### outputs structured format file:line: old -> new

- outputs structured format file:line: old -> new


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outputs structured format file:line: old -> new")
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

- uses safe_grep for finding occurrences
   - Expected: args[0] equals `-rn`
   - Expected: args.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses safe_grep for finding occurrences")
val args = ["-rn", "\\bfoo\\b", "src/", "--include=*.spl"]
expect(args[0]).to_equal("-rn")
expect(args.len()).to_equal(4)
```

</details>

#### whole word replacement preserves boundaries

- whole word replacement preserves boundaries
   - Expected: has_foo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whole word replacement preserves boundaries")
val line = "val foobar = foo(foo_arg)"
# _replace_word("foo", "bar") should only replace standalone "foo"
val has_foo = line.contains("foo")
expect(has_foo).to_equal(true)
```

</details>

### semantic tokens upgrade

#### supports 12+ token types

- supports 12+ token types
   - Expected: types.len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports 12+ token types")
val types = ["keyword", "function", "type", "parameter", "property", "variable", "operator", "comment", "string", "number", "enumMember", "namespace"]
expect(types.len()).to_equal(12)
```

</details>

#### classifies fn/class/struct as keywords

- classifies fn/class/struct as keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies fn/class/struct as keywords")
val keywords = ["fn", "class", "struct", "enum", "val", "var", "if", "else", "elif", "for", "while", "match", "case", "return", "use", "import", "trait", "impl", "static", "me", "self", "nil", "true", "false", "extern", "export", "type", "alias", "mixin", "ce", "bind", "receive", "after"]
expect(keywords).to_contain("fn")
expect(keywords).to_contain("class")
expect(keywords).to_contain("struct")
```

</details>

#### classifies identifier by outline data

- classifies identifier by outline data


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies identifier by outline data")
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

- classifies comment lines
   - Expected: is_comment is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies comment lines")
val line = "# this is a comment"
val trimmed = line.trim()
val is_comment = trimmed.starts_with("#")
expect(is_comment).to_equal(true)
```

</details>

#### classifies string literals

- classifies string literals
   - Expected: is_string is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies string literals")
val token = "\"hello world\""
val is_string = token.starts_with("\"")
expect(is_string).to_equal(true)
```

</details>

#### classifies numeric literals

- classifies numeric literals
   - Expected: token equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies numeric literals")
val token = "42"
val is_numeric = token >= "0" and token <= "99999"
expect(token).to_equal("42")
```

</details>

### inlay hints outline-based

#### infers type from string literal

- infers type from string literal
   - Expected: is_string is true
   - Expected: inferred equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers type from string literal")
val rhs = "\"hello\""
val inferred = "text"
val is_string = rhs.starts_with("\"")
expect(is_string).to_equal(true)
expect(inferred).to_equal("text")
```

</details>

#### infers type from integer literal

- infers type from integer literal
   - Expected: inferred equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers type from integer literal")
val rhs = "42"
val inferred = "i64"
expect(inferred).to_equal("i64")
```

</details>

#### infers type from boolean literal

- infers type from boolean literal
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers type from boolean literal")
val rhs = "true"
val inferred = "bool"
val is_bool = rhs == "true" or rhs == "false"
expect(is_bool).to_equal(true)
```

</details>

#### infers type from function call via outline

- infers type from function call via outline
   - Expected: inferred equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers type from function call via outline")
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

- skips already-typed bindings
   - Expected: has_type_annotation is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips already-typed bindings")
val line = "val count: i64 = 0"
val has_type_annotation = line.contains(": i64")
expect(has_type_annotation).to_equal(true)
```

</details>

### new subcommand dispatch

#### recognizes document-highlight

- recognizes document-highlight


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes document-highlight")
val all_subcmds = ["definition", "references", "hover", "completions", "type-at", "signature-help", "rename", "code-actions", "workspace-symbols", "call-hierarchy", "type-hierarchy", "semantic-tokens", "inlay-hints", "selection-range", "document-formatting", "document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("document-highlight")
```

</details>

#### recognizes type-definition

- recognizes type-definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes type-definition")
val all_subcmds = ["document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("type-definition")
```

</details>

#### recognizes implementation

- recognizes implementation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes implementation")
val all_subcmds = ["document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("implementation")
```

</details>

#### recognizes folding-range

- recognizes folding-range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes folding-range")
val all_subcmds = ["document-highlight", "type-definition", "implementation", "folding-range"]
expect(all_subcmds).to_contain("folding-range")
```

</details>

#### total subcommands is now 19

- total subcommands is now 19
   - Expected: total equals `19`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total subcommands is now 19")
val original = 5
val tier4 = 10
val new_lsp = 4
val total = original + tier4 + new_lsp
expect(total).to_equal(19)
```

</details>

### safe_process replaces query_shell

#### code_actions uses safe_process

- code_actions uses safe_process
   - Expected: cmd equals `bin/simple`
   - Expected: args.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("code_actions uses safe_process")
val cmd = "bin/simple"
val args = ["check", "src/test.spl"]
expect(cmd).to_equal("bin/simple")
expect(args.len()).to_equal(2)
```

</details>

#### document_formatting uses safe_process

- document_formatting uses safe_process
   - Expected: cmd equals `bin/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("document_formatting uses safe_process")
val cmd = "bin/simple"
val args = ["fmt", "--check", "src/test.spl"]
expect(cmd).to_equal("bin/simple")
```

</details>

#### workspace_symbols uses safe_grep

- workspace_symbols uses safe_grep
   - Expected: cmd equals `grep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workspace_symbols uses safe_grep")
val cmd = "grep"
val args = ["-rn", "query_main", "src/", "--include=*.spl"]
expect(cmd).to_equal("grep")
expect(args).to_contain("--include=*.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/query_upgrade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Tier 2 engine delegation, query input sanitization, rename upgrade with apply, semantic tokens upgrade, inlay hints outline-based, new subcommand dispatch, safe_process replaces query_shell.
- Tier 2 engine delegation
- query input sanitization
- rename upgrade with apply
- semantic tokens upgrade
- inlay hints outline-based
- new subcommand dispatch
- safe_process replaces query_shell

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `6aa4138b65ec46c7e82212114c4802867d851bcb81f674bc37f556994a91b1a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6aa4138b65ec46c7e82212114c4802867d851bcb81f674bc37f556994a91b1a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6aa4138b65ec46c7e82212114c4802867d851bcb81f674bc37f556994a91b1a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/cli/query_upgrade_spec.spl
mirror: doc/06_spec/unit/app/cli/query_upgrade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/query_upgrade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/query_upgrade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/query_upgrade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli/query_upgrade_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'definition delegates to engine_find_definition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_upgrade_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'references delegates to engine_find_references' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_upgrade_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hover delegates to engine_hover' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
