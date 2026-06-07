# Console Specification

> <details>

<!-- sdn-diagram:id=console_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=console_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

console_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=console_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Console Specification

## Scenarios

### GameConsole

#### creates an empty console

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val console = GameConsole.new(100)
expect(console.command_count()).to_equal(0)
expect(console.is_visible()).to_equal(false)
```

</details>

#### registers a command

1. var console = GameConsole new
2. console register command
   - Expected: console.command_count() equals `1`
   - Expected: console.has_command("help") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
console.register_command("help", "Show available commands")
expect(console.command_count()).to_equal(1)
expect(console.has_command("help")).to_equal(true)
```

</details>

#### reports missing commands

1. var console = GameConsole new
   - Expected: console.has_command("nope") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
expect(console.has_command("nope")).to_equal(false)
```

</details>

#### executes a registered command

1. var console = GameConsole new
2. console register command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
console.register_command("ping", "Pong!")
val output = console.execute("ping")
expect(output).to_contain("ping")
expect(output).to_contain("Pong!")
```

</details>

#### returns unknown for unregistered commands

1. var console = GameConsole new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
val output = console.execute("foo")
expect(output).to_contain("unknown command")
```

</details>

#### stores input and output in history

1. var console = GameConsole new
2. console register command
3. console execute
   - Expected: hist.len() equals `2`
   - Expected: hist[0].is_input is true
   - Expected: hist[0].content equals `test`
   - Expected: hist[1].is_input is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
console.register_command("test", "A test")
console.execute("test")
val hist = console.get_history()
expect(hist.len()).to_equal(2)
expect(hist[0].is_input).to_equal(true)
expect(hist[0].content).to_equal("test")
expect(hist[1].is_input).to_equal(false)
```

</details>

#### toggles visibility

1. var console = GameConsole new
   - Expected: console.is_visible() is false
2. console toggle
   - Expected: console.is_visible() is true
3. console toggle
   - Expected: console.is_visible() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
expect(console.is_visible()).to_equal(false)
console.toggle()
expect(console.is_visible()).to_equal(true)
console.toggle()
expect(console.is_visible()).to_equal(false)
```

</details>

#### adds output lines

1. var console = GameConsole new
2. console add output
   - Expected: hist.len() equals `1`
   - Expected: hist[0].content equals `Welcome to the console`
   - Expected: hist[0].is_input is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
console.add_output("Welcome to the console")
val hist = console.get_history()
expect(hist.len()).to_equal(1)
expect(hist[0].content).to_equal("Welcome to the console")
expect(hist[0].is_input).to_equal(false)
```

</details>

#### clears history

1. var console = GameConsole new
2. console add output
3. console add output
4. console clear history
   - Expected: console.get_history().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
console.add_output("line1")
console.add_output("line2")
console.clear_history()
expect(console.get_history().len()).to_equal(0)
```

</details>

#### trims history to max_history

1. var console = GameConsole new
2. console add output
3. console add output
4. console add output
5. console add output
   - Expected: hist.len() equals `3`
   - Expected: hist[0].content equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(3)
console.add_output("a")
console.add_output("b")
console.add_output("c")
console.add_output("d")
val hist = console.get_history()
expect(hist.len()).to_equal(3)
expect(hist[0].content).to_equal("b")
```

</details>

#### registers multiple commands

1. var console = GameConsole new
2. console register command
3. console register command
4. console register command
   - Expected: console.command_count() equals `3`
   - Expected: console.has_command("quit") is true
   - Expected: console.has_command("stats") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var console = GameConsole.new(100)
console.register_command("help", "Show help")
console.register_command("quit", "Exit game")
console.register_command("stats", "Show stats")
expect(console.command_count()).to_equal(3)
expect(console.has_command("quit")).to_equal(true)
expect(console.has_command("stats")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/console_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GameConsole

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
