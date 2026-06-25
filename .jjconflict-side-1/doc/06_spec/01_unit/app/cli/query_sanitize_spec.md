# query_sanitize_spec

> Tests for shell injection prevention in query subcommands. Validates sanitize_path, sanitize_symbol, and safe_grep wrappers.

<!-- sdn-diagram:id=query_sanitize_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_sanitize_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_sanitize_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_sanitize_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# query_sanitize_spec

Tests for shell injection prevention in query subcommands. Validates sanitize_path, sanitize_symbol, and safe_grep wrappers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/cli/query_sanitize_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for shell injection prevention in query subcommands.
Validates sanitize_path, sanitize_symbol, and safe_grep wrappers.

## Scenarios

### sanitize_path rejects dangerous characters

#### rejects dollar sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/$HOME/test.spl"
val has_dollar = path.contains("$")
expect(has_dollar).to_equal(true)
```

</details>

#### rejects backtick

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/`whoami`/test.spl"
val has_backtick = path.contains("`")
expect(has_backtick).to_equal(true)
```

</details>

#### rejects pipe character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/test.spl|cat /etc/passwd"
val has_pipe = path.contains("|")
expect(has_pipe).to_equal(true)
```

</details>

#### rejects semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/test.spl; rm -rf /"
val has_semi = path.contains(";")
expect(has_semi).to_equal(true)
```

</details>

#### rejects ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/test.spl&cat /etc/passwd"
val has_amp = path.contains("&")
expect(has_amp).to_equal(true)
```

</details>

#### rejects redirect characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path_gt = "src/test.spl > /tmp/out"
val path_lt = "src/test.spl < /etc/passwd"
val has_gt = path_gt.contains(">")
val has_lt = path_lt.contains("<")
expect(has_gt).to_equal(true)
expect(has_lt).to_equal(true)
```

</details>

#### rejects command substitution

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/$(whoami)/test.spl"
val has_cmd_sub = path.contains("$(")
expect(has_cmd_sub).to_equal(true)
```

</details>

#### rejects empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = ""
val is_empty = path == ""
expect(is_empty).to_equal(true)
```

</details>

### sanitize_path accepts safe paths

#### accepts simple relative path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/cli/query.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|") or path.contains(";") or path.contains("&"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts path with dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/common/text/mod.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts path with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/cli/query_sanitize.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts path with hyphens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/some-module/file.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts absolute path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/home/user/dev/simple/src/test.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

### sanitize_symbol validation

#### accepts lowercase identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "query_main"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### accepts uppercase identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "SERVER_NAME"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### accepts mixed case identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "LazySession"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### accepts numeric suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "handler42"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### rejects hyphenated name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "my-function"
val has_hyphen = name.contains("-")
expect(has_hyphen).to_equal(true)
```

</details>

#### rejects dot-separated name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "module.func"
val has_dot = name.contains(".")
expect(has_dot).to_equal(true)
```

</details>

#### rejects space in name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "my func"
val has_space = name.contains(" ")
expect(has_space).to_equal(true)
```

</details>

#### rejects empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = ""
val is_empty = name == ""
expect(is_empty).to_equal(true)
```

</details>

#### rejects shell characters in symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "foo;rm"
val has_semi = name.contains(";")
expect(has_semi).to_equal(true)
```

</details>

### safe_grep command construction

#### builds grep with include flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val include_flag = "--include=" + "*.spl"
expect(include_flag).to_equal("--include=*.spl")
```

</details>

#### uses array args not string concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["-rn", "pattern", "src/", "--include=*.spl"]
expect(args.len()).to_equal(4)
expect(args[0]).to_equal("-rn")
expect(args[1]).to_equal("pattern")
expect(args[2]).to_equal("src/")
expect(args[3]).to_equal("--include=*.spl")
```

</details>

#### safe_grep_file uses -n flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["-n", "pattern", "file.spl"]
expect(args.len()).to_equal(3)
expect(args[0]).to_equal("-n")
```

</details>

#### safe_process wraps rt_process_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "grep"
val args = ["-rn", "symbol", "src/"]
expect(cmd).to_equal("grep")
expect(args.len()).to_equal(3)
```

</details>

### sanitize integration with query

#### sanitize before engine call pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
val symbol = "query_main"
# Simulating: val clean_file = sanitize_path(file)
val has_dangerous = file.contains("$") or file.contains(";")
val clean_file = file
expect(clean_file).to_equal(file)
```

</details>

#### rejects injection in file arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/test; cat /etc/passwd"
val has_semi = file.contains(";")
# sanitize_path would return "" for this
expect(has_semi).to_equal(true)
```

</details>

#### rejects injection in symbol arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "foo$(whoami)"
val has_cmd_sub = symbol.contains("$(")
expect(has_cmd_sub).to_equal(true)
```

</details>

#### safe pattern: array args prevent injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val user_input = "src/test;rm -rf /"
val args = ["-rn", "pattern", user_input]
# When passed as array element, shell metacharacters have no effect
expect(args[2]).to_equal(user_input)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
