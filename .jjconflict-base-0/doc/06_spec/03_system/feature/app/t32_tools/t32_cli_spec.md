# T32 CLI Shell -- Parser, Error Code, and Type Tests

> Tests for the T32 CLI shell: text parsers (split, trim, find_char), error code builders with suggestion helpers, join utility, type constructors (T32WindowNode, T32Action, T32Field), and SDN catalog entry helpers.

<!-- sdn-diagram:id=t32_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 CLI Shell -- Parser, Error Code, and Type Tests

Tests for the T32 CLI shell: text parsers (split, trim, find_char), error code builders with suggestion helpers, join utility, type constructors (T32WindowNode, T32Action, T32Field), and SDN catalog entry helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-CLI-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/t32_tools/t32_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the T32 CLI shell: text parsers (split, trim, find_char),
error code builders with suggestion helpers, join utility,
type constructors (T32WindowNode, T32Action, T32Field),
and SDN catalog entry helpers.

## Source

`examples/10_tooling/trace32_tools/t32_cli/text_parser.spl`
`examples/10_tooling/trace32_tools/t32_cli/error_codes.spl`
`examples/10_tooling/trace32_tools/t32_cli/types.spl`

## Scenarios

### T32 CLI Text Parsers

#### split_lines

#### handles single line without newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = split_lines("single")
expect(lines[0]).to_equal("single")
expect(lines.len()).to_equal(1)
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = split_lines("")
expect(lines.len()).to_equal(0)
```

</details>

#### split_whitespace

#### splits on spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_whitespace("hello  world  test")
expect(parts[0]).to_equal("hello")
expect(parts.len()).to_equal(3)
expect(parts[1]).to_equal("world")
expect(parts[2]).to_equal("test")
```

</details>

#### handles leading and trailing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_whitespace("  hello  ")
expect(parts[0]).to_equal("hello")
expect(parts.len()).to_equal(1)
```

</details>

#### trim

#### removes leading spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = trim("   hello")
expect(result).to_equal("hello")
```

</details>

#### removes trailing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = trim("hello   ")
expect(result).to_equal("hello")
```

</details>

#### removes both sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = trim("  hello  ")
expect(result).to_equal("hello")
```

</details>

#### returns empty for whitespace-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = trim("   ")
expect(result).to_equal("")
```

</details>

#### find_char

#### finds first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = find_char("hello=world", '=')
expect(pos).to_equal(5)
```

</details>

#### returns -1 for missing char

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = find_char("hello world", '=')
expect(pos).to_equal(-1)
```

</details>

#### split_on

#### splits on delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_on("a:b:c", ":")
expect(parts[0]).to_equal("a")
expect(parts.len()).to_equal(3)
expect(parts[1]).to_equal("b")
expect(parts[2]).to_equal("c")
```

</details>

#### handles no delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_on("abc", ":")
expect(parts[0]).to_equal("abc")
expect(parts.len()).to_equal(1)
```

</details>

#### parse_tabular_output

#### parses single-line header with no data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "name  type  value"
val rows = parse_tabular_output(raw, " ")
expect(rows.len()).to_equal(0)
```

</details>

### T32 CLI Error Codes

#### error message builders

#### builds unknown command error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_cmd("xyz")
expect(msg).to_start_with("T4001:")
expect(msg).to_contain("xyz")
expect(msg).to_contain("Available:")
```

</details>

#### builds session not found error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_session_not_found("s99", ["s1", "s2"])
expect(msg).to_start_with("T4010:")
expect(msg).to_contain("s99")
expect(msg).to_contain("Available:")
```

</details>

#### builds duplicate session error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_session_duplicate("main", "s1")
expect(msg).to_start_with("T4011:")
expect(msg).to_contain("main")
expect(msg).to_contain("s1")
```

</details>

#### builds no active session error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_no_session()
expect(msg).to_start_with("T4013:")
expect(msg).to_contain("No active session")
```

</details>

#### suggestion helpers

#### suggests similar names by prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = ["sessions", "cores", "windows", "shell"]
val matches = t32_suggest_similar("se", candidates)
expect(matches[0]).to_equal("sessions")
expect(matches.len()).to_be_greater_than(0)
```

</details>

#### returns empty for no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = t32_suggest_similar("zzz", ["alpha", "beta"])
expect(matches.len()).to_equal(0)
```

</details>

#### builds did-you-mean hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = t32_did_you_mean("ses", ["sessions", "cores"])
expect(hint).to_contain("Did you mean:")
expect(hint).to_contain("sessions")
```

</details>

#### returns empty hint when no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hint = t32_did_you_mean("zzz", ["alpha", "beta"])
expect(hint).to_equal("")
```

</details>

#### join_list

#### joins empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_join_list([], ", ")
expect(result).to_equal("")
```

</details>

#### joins single item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_join_list(["hello"], ", ")
expect(result).to_equal("hello")
```

</details>

#### joins multiple items

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_join_list(["a", "b", "c"], ", ")
expect(result).to_equal("a, b, c")
```

</details>

#### cli_commands list

#### contains expected commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = cli_commands()
expect(cmds).to_contain("sessions")
expect(cmds).to_contain("help")
expect(cmds).to_contain("shell")
```

</details>

### T32 CLI SDN Catalog Helpers

#### entry_get

#### returns empty for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: Dict<text, text> = {}
val result = entry_get(d, "missing")
expect(result).to_equal("")
```

</details>

### T32 CLI Type System

#### T32WindowNode

#### creates with key and title

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val win = T32WindowNode.create("break_list", "Breakpoints", "built_in", "print_parse")
expect(win.window_key).to_equal("break_list")
expect(win.title).to_equal("Breakpoints")
expect(win.kind).to_equal("built_in")
expect(win.capture_mode).to_equal("print_parse")
```

</details>

#### creates built-in with commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val win = T32WindowNode.built_in("regs", "Registers", "Register.view", "Register.dump")
expect(win.window_key).to_equal("regs")
expect(win.open_command).to_equal("Register.view")
expect(win.capture_command).to_equal("Register.dump")
expect(win.kind).to_equal("built_in")
```

</details>

#### T32Action

#### creates with command template

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val action = T32Action.create("step_into", "Step Into", "execute", "Step")
expect(action.action_key).to_equal("step_into")
expect(action.label).to_equal("Step Into")
expect(action.command_template).to_equal("Step")
```

</details>

#### creates execute action

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val action = T32Action.execute("go", "Run", "Go")
expect(action.action_type).to_equal("execute")
expect(action.command_template).to_equal("Go")
```

</details>

#### creates open_window action

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val action = T32Action.open_window("show_regs", "Show Registers", "Register.view", "regs")
expect(action.action_type).to_equal("open_window")
expect(action.target_window_key).to_equal("regs")
```

</details>

#### T32Field

#### creates with scope and type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = T32Field.create("bp_address", "Address", "hex", "window")
expect(field.field_key).to_equal("bp_address")
expect(field.label).to_equal("Address")
expect(field.value_type).to_equal("hex")
expect(field.scope).to_equal("window")
```

</details>

#### T32Catalogs

#### creates empty catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cat = T32Catalogs.empty()
expect(cat.windows.len()).to_equal(0)
expect(cat.actions.len()).to_equal(0)
expect(cat.fields.len()).to_equal(0)
```

</details>

#### finds window by key

1. var cat = T32Catalogs empty
2. cat windows push


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cat = T32Catalogs.empty()
val win = T32WindowNode.create("test_win", "Test", "built_in", "print_parse")
cat.windows.push(win)
val found = cat.find_window("test_win")
match found:
    Some(w): expect(w.title).to_equal("Test")
    nil: expect("should find window").to_equal("found")
```

</details>

#### returns nil for missing window

1. Some
   - Expected: is_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cat = T32Catalogs.empty()
val found = cat.find_window("nonexistent")
var is_nil = false
match found:
    Some(w): is_nil = false
    nil: is_nil = true
expect(is_nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
