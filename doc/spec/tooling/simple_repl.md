# simple_repl - Interactive REPL

## Overview

Interactive Read-Eval-Print-Loop for exploring Simple language. Implemented in pure Simple using temp-file accumulation and subprocess execution.

## Usage

```bash
# Start the REPL
bin/release/simple src/app/repl/main.spl

# Via CLI dispatch
bin/simple repl
```

## REPL Session

```
Simple Language REPL v0.2.0
Type ':help' for commands, ':quit' to exit

>>> val x = 42
>>> print x
42

>>> 2 + 3
5

>>> fn double(n: i64) -> i64:
...     n * 2
...

>>> print double(21)
42

>>> :quit
Goodbye!
```

## Commands

| Command | Description |
|---------|-------------|
| `:help`, `:h` | Show help |
| `:quit`, `:q`, `:exit` | Exit REPL |
| `:clear` | Clear accumulated state |
| `:history` | Show command history |
| `:show` | Show accumulated definitions |
| `:load <file>` | Load and execute file |
| `exit`, `quit`, `exit()`, `quit()` | Exit (without colon prefix) |

## Features

### Multi-line Input

Lines ending with `:` enter continuation mode. Empty line submits block:

```
>>> fn factorial(n: i64) -> i64:
...     if n <= 1:
...         return 1
...     n * factorial(n - 1)
...

>>> print factorial(5)
120
```

### State Persistence

Declarations persist across evaluations:

```
>>> val config = "debug"
>>> fn is_debug() -> bool:
...     config == "debug"
...

>>> print is_debug()
true
```

### Expression Auto-print

Bare expressions are automatically wrapped and printed:

```
>>> 2 + 3
5
>>> "hello".len()
5
```

### Error Recovery

Invalid input shows an error but doesn't crash:

```
>>> this is not valid
Error: ...

>>> print "still alive"
still alive
```

## Evaluation Strategy

1. **Declarations** (`val`, `var`, `fn`, `class`, etc.): Appended to accumulated state, re-run via subprocess
2. **Statements** (`if`, `while`, `for`, `print`, assignments): Appended to accumulated state
3. **Expressions** (anything else): Wrapped in `fn __repl_expr_N()` helper, not persisted
4. **Failures**: Rolled back to previous accumulated state

## Implementation Notes

- **Source:** `src/app/repl/main.spl` (249 lines)
- **No compiler imports:** Uses `bin/release/simple` subprocess for fast startup
- **Module-level state:** `var` declarations at module level (avoids closure mutation bug)
- **Text accumulation:** Uses `text` concatenation (avoids `.len()`/`.push()` array path call bug)
- **Temp file:** `/tmp/simple_repl_{pid}.spl`
- **Subprocess:** `rt_process_run("bash", ["-c", "bin/release/simple path </dev/null 2>&1"])`

## Dependencies

- `bin/release/simple` binary
- Runtime extern functions: `input()`, `stdout_write()`, `stdout_flush()`, `rt_file_write_text()`, `rt_file_delete()`, `rt_file_exists()`, `rt_getpid()`, `rt_process_run()`, `rt_file_read_text()`

## Test Files

| File | Tests |
|------|-------|
| `test/system/repl/repl_basic_eval_system_spec.spl` | 5 |
| `test/system/repl/repl_state_persistence_system_spec.spl` | 3 |
| `test/system/repl/repl_multiline_system_spec.spl` | 2 |
| `test/system/repl/repl_error_recovery_system_spec.spl` | 2 |
| `test/system/repl/repl_commands_system_spec.spl` | 7 |
