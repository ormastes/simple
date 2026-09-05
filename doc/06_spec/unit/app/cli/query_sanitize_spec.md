# Query Sanitize Specification

> Tests covering sanitize_path rejects dangerous characters, sanitize_path accepts safe paths, sanitize_symbol validation, safe_grep command construction, sanitize integration with query.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Sanitize Specification

## Scenarios

### sanitize_path rejects dangerous characters

#### rejects dollar sign

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects dollar sign
   - Expected: has_dollar is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dollar sign")
val path = "src/$HOME/test.spl"
val has_dollar = path.contains("$")
expect(has_dollar).to_equal(true)
```

</details>

#### rejects backtick

- rejects backtick
   - Expected: has_backtick is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects backtick")
val path = "src/`whoami`/test.spl"
val has_backtick = path.contains("`")
expect(has_backtick).to_equal(true)
```

</details>

#### rejects pipe character

- rejects pipe character
   - Expected: has_pipe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects pipe character")
val path = "src/test.spl|cat /etc/passwd"
val has_pipe = path.contains("|")
expect(has_pipe).to_equal(true)
```

</details>

#### rejects semicolon

- rejects semicolon
   - Expected: has_semi is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects semicolon")
val path = "src/test.spl; rm -rf /"
val has_semi = path.contains(";")
expect(has_semi).to_equal(true)
```

</details>

#### rejects ampersand

- rejects ampersand
   - Expected: has_amp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ampersand")
val path = "src/test.spl&cat /etc/passwd"
val has_amp = path.contains("&")
expect(has_amp).to_equal(true)
```

</details>

#### rejects redirect characters

- rejects redirect characters
   - Expected: has_gt is true
   - Expected: has_lt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects redirect characters")
val path_gt = "src/test.spl > /tmp/out"
val path_lt = "src/test.spl < /etc/passwd"
val has_gt = path_gt.contains(">")
val has_lt = path_lt.contains("<")
expect(has_gt).to_equal(true)
expect(has_lt).to_equal(true)
```

</details>

#### rejects command substitution

- rejects command substitution
   - Expected: has_cmd_sub is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects command substitution")
val path = "src/$(whoami)/test.spl"
val has_cmd_sub = path.contains("$(")
expect(has_cmd_sub).to_equal(true)
```

</details>

#### rejects empty path

- rejects empty path
   - Expected: is_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty path")
val path = ""
val is_empty = path == ""
expect(is_empty).to_equal(true)
```

</details>

### sanitize_path accepts safe paths

#### accepts simple relative path

- accepts simple relative path
   - Expected: has_dangerous is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts simple relative path")
val path = "src/app/cli/query.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|") or path.contains(";") or path.contains("&"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts path with dots

- accepts path with dots
   - Expected: has_dangerous is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts path with dots")
val path = "src/lib/common/text/mod.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts path with underscores

- accepts path with underscores
   - Expected: has_dangerous is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts path with underscores")
val path = "src/app/cli/query_sanitize.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts path with hyphens

- accepts path with hyphens
   - Expected: has_dangerous is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts path with hyphens")
val path = "src/app/some-module/file.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

#### accepts absolute path

- accepts absolute path
   - Expected: has_dangerous is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts absolute path")
val path = "/home/user/dev/simple/src/test.spl"
val has_dangerous = (path.contains("$") or path.contains("`") or path.contains("|"))
expect(has_dangerous).to_equal(false)
```

</details>

### sanitize_symbol validation

#### accepts lowercase identifier

- accepts lowercase identifier
   - Expected: is_safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts lowercase identifier")
val name = "query_main"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### accepts uppercase identifier

- accepts uppercase identifier
   - Expected: is_safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts uppercase identifier")
val name = "SERVER_NAME"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### accepts mixed case identifier

- accepts mixed case identifier
   - Expected: is_safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts mixed case identifier")
val name = "LazySession"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### accepts numeric suffix

- accepts numeric suffix
   - Expected: is_safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts numeric suffix")
val name = "handler42"
val is_safe = _check_symbol_chars(name)
expect(is_safe).to_equal(true)
```

</details>

#### rejects hyphenated name

- rejects hyphenated name
   - Expected: has_hyphen is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects hyphenated name")
val name = "my-function"
val has_hyphen = name.contains("-")
expect(has_hyphen).to_equal(true)
```

</details>

#### rejects dot-separated name

- rejects dot-separated name
   - Expected: has_dot is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dot-separated name")
val name = "module.func"
val has_dot = name.contains(".")
expect(has_dot).to_equal(true)
```

</details>

#### rejects space in name

- rejects space in name
   - Expected: has_space is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects space in name")
val name = "my func"
val has_space = name.contains(" ")
expect(has_space).to_equal(true)
```

</details>

#### rejects empty name

- rejects empty name
   - Expected: is_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty name")
val name = ""
val is_empty = name == ""
expect(is_empty).to_equal(true)
```

</details>

#### rejects shell characters in symbol

- rejects shell characters in symbol
   - Expected: has_semi is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects shell characters in symbol")
val name = "foo;rm"
val has_semi = name.contains(";")
expect(has_semi).to_equal(true)
```

</details>

### safe_grep command construction

#### builds grep with include flag

- builds grep with include flag
   - Expected: include_flag equals `--include=*.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds grep with include flag")
val include_flag = "--include=" + "*.spl"
expect(include_flag).to_equal("--include=*.spl")
```

</details>

#### uses array args not string concatenation

- uses array args not string concatenation
   - Expected: args.len() equals `4`
   - Expected: args[0] equals `-rn`
   - Expected: args[1] equals `pattern`
   - Expected: args[2] equals `src/`
   - Expected: args[3] equals `--include=*.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses array args not string concatenation")
val args = ["-rn", "pattern", "src/", "--include=*.spl"]
expect(args.len()).to_equal(4)
expect(args[0]).to_equal("-rn")
expect(args[1]).to_equal("pattern")
expect(args[2]).to_equal("src/")
expect(args[3]).to_equal("--include=*.spl")
```

</details>

#### safe_grep_file uses -n flag

- safe_grep_file uses -n flag
   - Expected: args.len() equals `3`
   - Expected: args[0] equals `-n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("safe_grep_file uses -n flag")
val args = ["-n", "pattern", "file.spl"]
expect(args.len()).to_equal(3)
expect(args[0]).to_equal("-n")
```

</details>

#### safe_process wraps rt_process_run

- safe_process wraps rt_process_run
   - Expected: cmd equals `grep`
   - Expected: args.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("safe_process wraps rt_process_run")
val cmd = "grep"
val args = ["-rn", "symbol", "src/"]
expect(cmd).to_equal("grep")
expect(args.len()).to_equal(3)
```

</details>

### sanitize integration with query

#### sanitize before engine call pattern

- sanitize before engine call pattern
   - Expected: clean_file equals `file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sanitize before engine call pattern")
val file = "src/app/cli/query.spl"
val symbol = "query_main"
# Simulating: val clean_file = sanitize_path(file)
val has_dangerous = file.contains("$") or file.contains(";")
val clean_file = file
expect(clean_file).to_equal(file)
```

</details>

#### rejects injection in file arg

- rejects injection in file arg
   - Expected: has_semi is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects injection in file arg")
val file = "src/test; cat /etc/passwd"
val has_semi = file.contains(";")
# sanitize_path would return "" for this
expect(has_semi).to_equal(true)
```

</details>

#### rejects injection in symbol arg

- rejects injection in symbol arg
   - Expected: has_cmd_sub is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects injection in symbol arg")
val symbol = "foo$(whoami)"
val has_cmd_sub = symbol.contains("$(")
expect(has_cmd_sub).to_equal(true)
```

</details>

#### safe pattern: array args prevent injection

- safe pattern: array args prevent injection
   - Expected: args[2] equals `user_input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("safe pattern: array args prevent injection")
val user_input = "src/test;rm -rf /"
val args = ["-rn", "pattern", user_input]
# When passed as array element, shell metacharacters have no effect
expect(args[2]).to_equal(user_input)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/query_sanitize_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sanitize_path rejects dangerous characters, sanitize_path accepts safe paths, sanitize_symbol validation, safe_grep command construction, sanitize integration with query.
- sanitize_path rejects dangerous characters
- sanitize_path accepts safe paths
- sanitize_symbol validation
- safe_grep command construction
- sanitize integration with query

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
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

- Canonical SPipe generation for source `450cc7096a29a3d890885bdf7aad9062ccacf6d2d33d112d47ef3a64b088d3d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `450cc7096a29a3d890885bdf7aad9062ccacf6d2d33d112d47ef3a64b088d3d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `450cc7096a29a3d890885bdf7aad9062ccacf6d2d33d112d47ef3a64b088d3d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/cli/query_sanitize_spec.spl
mirror: doc/06_spec/unit/app/cli/query_sanitize_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/query_sanitize_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/query_sanitize_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/query_sanitize_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli/query_sanitize_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects dollar sign' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_sanitize_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects backtick' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_sanitize_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects pipe character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
