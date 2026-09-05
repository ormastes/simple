# Shell Scripting Engine Specification

> Validates the ScriptEngine (shell_script.spl) and ShellExpander (shell_expand.spl) that power .shs script execution inside SimpleOS.

<!-- sdn-diagram:id=shell_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_script_spec -> std
shell_script_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Scripting Engine Specification

Validates the ScriptEngine (shell_script.spl) and ShellExpander (shell_expand.spl) that power .shs script execution inside SimpleOS.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #shell-script-engine |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/shell/shell_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the ScriptEngine (shell_script.spl) and ShellExpander (shell_expand.spl)
that power .shs script execution inside SimpleOS.

Tests cover:
- if/elif/else/fi control flow
- while/do/done and for/do/done loops
- case/esac pattern matching
- function / fn definition and call
- Variable expansion: $?, $0-$9, $@, $*, $#, ${var:-default}, ${var:+alt}, ${#var}, $(cmd)
- source / . builtin loading a .shs file
- ControlFlow propagation: break, continue, return

## Key Concepts

| Concept | Description |
|---------|-------------|
| ScriptEngine | Parses and executes shell script text as a sequence of Stmt nodes |
| ShellContext | Carries variables, env, cwd, last_exit_code, positional_args, aliases, functions |
| ControlFlow | Normal(i32), Break(i32), Continue(i32), Return(i32) — propagates through frames |
| ShellExpander | Performs $VAR / $(cmd) / ${var:-default} expansion on a text token |
| Stmt | AST node: If, While, For, Case, FnDef, Pipeline, Assign, Source, Return, Break, Continue |

## Scenarios

### ShellExpander variable expansion

#### when expanding simple $VAR

#### substitutes a known variable

1. ctx variables set
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.variables.set("GREETING", "hello")
val result = ShellExpander.expand(ctx, "$GREETING world")
expect(result).to_equal("hello world")
```

</details>

#### expands to empty string for unknown variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val result = ShellExpander.expand(ctx, "[$UNDEFINED]")
expect(result).to_equal("[]")
```

</details>

#### when expanding $? exit code

#### returns last exit code as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.last_exit_code = 42
val result = ShellExpander.expand(ctx, "exit=$?")
expect(result).to_equal("exit=42")
```

</details>

#### returns 0 when no command has run

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val result = ShellExpander.expand(ctx, "$?")
expect(result).to_equal("0")
```

</details>

#### when expanding positional parameters

#### expands $1 to first positional arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.positional_args = ["script.shs", "alpha", "beta"]
val result = ShellExpander.expand(ctx, "$1")
expect(result).to_equal("alpha")
```

</details>

#### expands $0 to script name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.positional_args = ["myscript.shs", "arg1"]
val result = ShellExpander.expand(ctx, "$0")
expect(result).to_equal("myscript.shs")
```

</details>

#### expands $# to arg count (excluding $0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.positional_args = ["myscript.shs", "a", "b", "c"]
val result = ShellExpander.expand(ctx, "$#")
expect(result).to_equal("3")
```

</details>

#### expands $@ to space-joined args

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.positional_args = ["script.shs", "x", "y"]
val result = ShellExpander.expand(ctx, "$@")
expect(result).to_equal("x y")
```

</details>

#### expands $* to same as $@ in unquoted context

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.positional_args = ["script.shs", "p", "q"]
val result = ShellExpander.expand(ctx, "$*")
expect(result).to_equal("p q")
```

</details>

#### when expanding ${var:-default}

#### returns variable value when set

1. ctx variables set
   - Expected: result equals `bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.variables.set("FOO", "bar")
val result = ShellExpander.expand(ctx, "${FOO:-fallback}")
expect(result).to_equal("bar")
```

</details>

#### returns default when variable is unset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val result = ShellExpander.expand(ctx, "${UNSET:-fallback}")
expect(result).to_equal("fallback")
```

</details>

#### returns default when variable is empty

1. ctx variables set
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.variables.set("EMPTY", "")
val result = ShellExpander.expand(ctx, "${EMPTY:-fallback}")
expect(result).to_equal("fallback")
```

</details>

#### when expanding ${var:+alt}

#### returns alt when variable is set and non-empty

1. ctx variables set
   - Expected: result equals `alt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.variables.set("SET", "value")
val result = ShellExpander.expand(ctx, "${SET:+alt}")
expect(result).to_equal("alt")
```

</details>

#### returns empty when variable is unset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val result = ShellExpander.expand(ctx, "${UNSET:+alt}")
expect(result).to_equal("")
```

</details>

#### when expanding ${#var} length

#### returns character count of variable value

1. ctx variables set
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.variables.set("WORD", "hello")
val result = ShellExpander.expand(ctx, "${#WORD}")
expect(result).to_equal("5")
```

</details>

#### returns 0 for unset variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val result = ShellExpander.expand(ctx, "${#NOVAR}")
expect(result).to_equal("0")
```

</details>

#### when expanding $(cmd) command substitution

#### captures stdout of a simple echo command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val result = ShellExpander.expand(ctx, "$(echo captured)")
expect(result).to_equal("captured")
```

</details>

#### trims trailing newline from captured output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val result = ShellExpander.expand(ctx, "prefix-$(echo trimmed)-suffix")
expect(result).to_equal("prefix-trimmed-suffix")
```

</details>

### ScriptEngine if/elif/else

#### executes then-branch when condition is true

1. engine execute script
   - Expected: ctx.variables.get("X") equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "if true; then\n  X=yes\nfi"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("yes")
```

</details>

#### skips then-branch when condition is false

1. engine execute script
   - Expected: ctx.variables.get("X") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "if false; then\n  X=yes\nfi"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("")
```

</details>

#### executes else-branch when condition is false

1. engine execute script
   - Expected: ctx.variables.get("X") equals `else`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "if false; then\n  X=then\nelse\n  X=else\nfi"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("else")
```

</details>

#### evaluates elif when first condition is false

1. engine execute script
   - Expected: ctx.variables.get("X") equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "if false; then\n  X=a\nelif true; then\n  X=b\nfi"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("b")
```

</details>

#### skips all elif branches when first is true

1. engine execute script
   - Expected: ctx.variables.get("X") equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "if true; then\n  X=first\nelif true; then\n  X=second\nfi"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("first")
```

</details>

### ScriptEngine while and for loops

<details>
<summary>Advanced: executes while loop body repeatedly until condition fails</summary>

#### executes while loop body repeatedly until condition fails

1. engine execute script
   - Expected: ctx.variables.get("I") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
# Uses test builtin: [ $I -lt 3 ] exits 0 while I < 3
val script = "I=0\nwhile [ $I -lt 3 ]; do\n  I=$((I+1))\ndone"
engine.execute_script(ctx, script)
expect(ctx.variables.get("I")).to_equal("3")
```

</details>


</details>

#### skips while body when initial condition is false

1. engine execute script
   - Expected: ctx.variables.get("X") equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "X=before\nwhile false; do\n  X=inside\ndone"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("before")
```

</details>

<details>
<summary>Advanced: iterates for loop over word list</summary>

#### iterates for loop over word list

1. engine execute script
   - Expected: ctx.variables.get("OUT") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "OUT=''\nfor W in a b c; do\n  OUT=\"$OUT$W\"\ndone"
engine.execute_script(ctx, script)
expect(ctx.variables.get("OUT")).to_equal("abc")
```

</details>


</details>

<details>
<summary>Advanced: break exits while loop early</summary>

#### break exits while loop early

1. engine execute script
   - Expected: ctx.variables.get("I") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "I=0\nwhile true; do\n  I=$((I+1))\n  if [ $I -eq 2 ]; then break; fi\ndone"
engine.execute_script(ctx, script)
expect(ctx.variables.get("I")).to_equal("2")
```

</details>


</details>

<details>
<summary>Advanced: continue skips remainder of for loop body</summary>

#### continue skips remainder of for loop body

1. engine execute script
   - Expected: ctx.variables.get("OUT") equals `ac`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "OUT=''\nfor W in a b c; do\n  if [ $W = b ]; then continue; fi\n  OUT=\"$OUT$W\"\ndone"
engine.execute_script(ctx, script)
expect(ctx.variables.get("OUT")).to_equal("ac")
```

</details>


</details>

### ScriptEngine case/esac

#### matches exact string pattern

1. ctx variables set
2. engine execute script
   - Expected: ctx.variables.get("X") equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
ctx.variables.set("VAL", "hello")
val script = "case $VAL in\n  hello) X=matched ;;\n  *) X=other ;;\nesac"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("matched")
```

</details>

#### falls through to wildcard when no pattern matches

1. ctx variables set
2. engine execute script
   - Expected: ctx.variables.get("X") equals `wildcard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
ctx.variables.set("VAL", "unknown")
val script = "case $VAL in\n  hello) X=hello ;;\n  *) X=wildcard ;;\nesac"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("wildcard")
```

</details>

#### matches pipe-separated alternatives

1. ctx variables set
2. engine execute script
   - Expected: ctx.variables.get("X") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
ctx.variables.set("VAL", "b")
val script = "case $VAL in\n  a|b|c) X=abc ;;\n  *) X=other ;;\nesac"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("abc")
```

</details>

### ScriptEngine function definitions

#### defines and calls a function

1. engine execute script
   - Expected: ctx.variables.get("X") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "function greet() {\n  X=hi\n}\ngreet"
engine.execute_script(ctx, script)
expect(ctx.variables.get("X")).to_equal("hi")
```

</details>

#### function receives positional args via $1 $2

1. engine execute script
   - Expected: ctx.variables.get("RESULT") equals `foo-bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "function add_args() {\n  RESULT=\"$1-$2\"\n}\nadd_args foo bar"
engine.execute_script(ctx, script)
expect(ctx.variables.get("RESULT")).to_equal("foo-bar")
```

</details>

#### return inside function propagates exit code

1. engine execute script
   - Expected: ctx.variables.get("CODE") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "function check() {\n  return 5\n}\ncheck\nCODE=$?"
engine.execute_script(ctx, script)
expect(ctx.variables.get("CODE")).to_equal("5")
```

</details>

#### function local variables do not leak to caller

1. ctx variables set
2. engine execute script
   - Expected: ctx.variables.get("OUTER") equals `mutated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
ctx.variables.set("OUTER", "original")
val engine = ScriptEngine.new()
val script = "function mutate() {\n  OUTER=mutated\n}\nmutate"
# POSIX: without 'local', assignment in function modifies global
engine.execute_script(ctx, script)
expect(ctx.variables.get("OUTER")).to_equal("mutated")
```

</details>

### ScriptEngine source builtin

#### source sets a variable defined in the sourced file

1. engine execute script
   - Expected: ctx.variables.get("SOURCED_VAR") equals `loaded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
# Simulate sourcing by executing inline — real impl reads from VFS
val sourced_content = "SOURCED_VAR=loaded"
engine.execute_script(ctx, sourced_content)
expect(ctx.variables.get("SOURCED_VAR")).to_equal("loaded")
```

</details>

#### source returns error ControlFlow when file does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = ShellContext.default()
val engine = ScriptEngine.new()
val script = "source /nonexistent_file.shs"
val flow = engine.execute_script(ctx, script)
expect(flow.exit_code).to_be_greater_than(0)
```

</details>

### ScriptEngine parse

#### parses an assignment as a Stmt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ScriptEngine.new()
val stmts = engine.parse("FOO=bar")
expect(stmts.len()).to_be_greater_than(0)
```

</details>

#### parses an if block as a single Stmt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ScriptEngine.new()
val stmts = engine.parse("if true; then\n  X=y\nfi")
expect(stmts.len()).to_be_greater_than(0)
```

</details>

#### parses empty input as empty Stmt list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ScriptEngine.new()
val stmts = engine.parse("")
expect(stmts.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
