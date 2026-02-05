# simple_repl - Interactive REPL

## Overview

Interactive Read-Eval-Print-Loop for exploring Simple language.

## Usage

```bash
simple_repl                        # Start REPL
simple_repl --load file.spl        # Load file before starting
simple_repl --no-prelude           # Don't load prelude
```

## Options

| Flag | Description |
|------|-------------|
| `--load <file>` | Load file before starting |
| `--no-prelude` | Don't auto-import prelude |
| `--no-colors` | Disable syntax highlighting |
| `--history <file>` | History file location |

## REPL Session

```
Simple REPL v0.1.0
Type :help for commands, :quit to exit

>>> let x = 42
42

>>> x * 2
84

>>> fn double(n: Int) -> Int:
...     return n * 2
...
<function double>

>>> double(21)
42

>>> import core.json

>>> json.parse('{"name": "test"}')
Ok({"name": "test"})

>>> :type x
Int

>>> :quit
Goodbye!
```

## Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help |
| `:quit` / `:q` | Exit REPL |
| `:clear` | Clear screen |
| `:reset` | Reset environment |
| `:load <file>` | Load and execute file |
| `:type <expr>` | Show type of expression |
| `:doc <name>` | Show documentation |
| `:history` | Show command history |
| `:save <file>` | Save session to file |

## Features

### Multi-line Input

```
>>> fn factorial(n: Int) -> Int:
...     if n <= 1:
...         return 1
...     return n * factorial(n - 1)
...
<function factorial>

>>> factorial(5)
120
```

### Tab Completion

```
>>> json.<TAB>
json.parse    json.stringify    json.Value

>>> let s = "hello"
>>> s.<TAB>
s.len    s.trim    s.split    s.replace    s.upper    s.lower
```

### History Navigation

- Up/Down arrows: Navigate history
- Ctrl+R: Reverse search
- History persists across sessions

### Syntax Highlighting

- Keywords in blue
- Strings in green
- Numbers in cyan
- Comments in gray
- Errors in red

## Implementation Notes

1. Line editing: Use readline-like library or custom
2. Multi-line detection: Track open brackets, colons
3. Evaluation: Use interpreter with persistent environment
4. Completion: Parse current scope for available names
5. History: Save to `~/.simple_history`

## Environment

Variables and functions defined in REPL persist:

```
>>> let config = {"debug": true}
>>> fn is_debug() -> Bool:
...     return config["debug"]
...
>>> is_debug()
true
```

## Error Handling

```
>>> 1 / 0
Error: Division by zero

>>> undefined_var
Error: Undefined variable 'undefined_var'

>>> fn bad():
...     return
...
Error: Missing return value
```

## Dependencies

- Interpreter integration
- Line editing (readline-like)
- Terminal handling (colors, cursor)
- `sys_get_args` - Command-line arguments

## Example Session

```
$ simple_repl --load mylib.spl

Simple REPL v0.1.0
Loaded: mylib.spl (3 functions, 1 class)
Type :help for commands, :quit to exit

>>> MyClass.new("test")
MyClass { name: "test" }

>>> :type MyClass
class MyClass

>>> :doc MyClass.new
Creates a new MyClass instance.

@param name: The name for this instance
@returns: A new MyClass

>>> :quit
Goodbye!
```
