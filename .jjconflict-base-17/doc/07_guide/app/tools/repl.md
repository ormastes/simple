# REPL Guide

Interactive Read-Eval-Print Loop for the Simple language.

---

## Quick Start

```bash
# Start the REPL
bin/simple run src/app/repl/main.spl

# Or via CLI dispatch (if wired)
bin/simple repl
```

```
Simple Language REPL v0.2.0
Type ':help' for commands, ':quit' to exit

>>> val x = 42
>>> print x
42
>>> 2 + 3
5
>>> :quit
Goodbye!
```

---

## Commands

| Command | Description |
|---------|-------------|
| `:help`, `:h` | Show help |
| `:quit`, `:q`, `:exit` | Exit REPL |
| `:clear` | Clear accumulated state |
| `:history` | Show command history |
| `:show` | Show accumulated definitions |
| `:load <file>` | Load and execute a `.spl` file |
| `exit`, `quit`, `exit()`, `quit()` | Exit (without colon prefix) |

---

## Evaluation Rules

### Declarations

Declarations are added to accumulated state and persist across evaluations:

```
>>> val x = 42
>>> var y = 10
>>> fn double(n: i64) -> i64:
...     n * 2
...
>>> print double(x)
84
```

Recognized declarations: `val`, `var`, `fn`, `class`, `struct`, `enum`, `trait`, `use`, `extern`, `type`, `alias`.

### Statements

Statements execute immediately using accumulated state:

```
>>> val x = 10
>>> if x > 5:
...     print "big"
...
big
>>> print "hello {x}"
hello 10
```

Recognized statements: `if`, `while`, `for`, `match`, `print`, assignments (`x = value`).

### Expressions

Expressions are auto-printed (wrapped in a helper function):

```
>>> 2 + 3
5
>>> "hello".len()
5
```

---

## Multi-line Input

Lines ending with `:` enter multi-line (continuation) mode. An empty line submits the block:

```
>>> fn greet(name: text) -> text:
...     "Hello, {name}!"
...
>>> print greet("World")
Hello, World!
```

---

## State Management

The REPL accumulates all successful declarations in a temp file (`/tmp/simple_repl_{pid}.spl`). Each evaluation re-runs the entire accumulated program via subprocess.

- **`:clear`** resets all accumulated state
- **`:show`** displays current accumulated definitions
- **`:load <file>`** appends a file's contents to accumulated state
- **Failed evaluations** are rolled back (state is preserved)

---

## Architecture

```
User Input
    |
    v
REPL Main Loop (src/app/repl/main.spl)
    |
    +-- Declaration? --> Append to accumulated code
    +-- Statement?   --> Append to accumulated code
    +-- Expression?  --> Wrap in fn __repl_expr_N()
    |
    v
Write temp file (/tmp/simple_repl_{pid}.spl)
    |
    v
rt_process_run("bin/simple", ["run", temp_file])
    |
    +-- Success --> Print output, keep in accumulated
    +-- Failure --> Print error, rollback
```

**Key design decisions:**
- No compiler imports (avoids 40s+ startup from loading full compiler tree)
- Subprocess execution via `bin/simple` or `bin/release/<platform>/simple` for isolation
- Module-level `var` state (avoids nested closure mutation bug)
- Text accumulation instead of arrays (avoids `.len()`/`.push()` path call issues)

---

## Source Files

| File | Purpose |
|------|---------|
| `src/app/repl/main.spl` | REPL implementation (249 lines) |
| `src/app/io/cli_commands.spl` | CLI wiring (`cli_run_repl`) |

---

## Related

- [CLI Guide](../cli.md) — command-line interface
- [Jupyter Guide](jupyter.md) — Jupyter notebook kernel
- [REPL Spec](../../spec/tooling/simple_repl.md) — specification
