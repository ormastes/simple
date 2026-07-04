# What Happens When Typing Two If Statements

## Scenario: User types this in TUI REPL

```python
>>> if x > 0:
...     if y > 0:
...         print("both positive")
```

---

## Expected Debug Log

### Line 1: Type "if x > 0:"

#### Character by character:
```
[DEBUG] Key received: i
[DEBUG] InsertChar 'i': before len=0, cap=0
[DEBUG]   after len=1, cap=8, reallocated=true
[DEBUG] RENDER: buffer 'i'

[DEBUG] Key received: f
[DEBUG] InsertChar 'f': before len=1, cap=8
[DEBUG]   after len=2, cap=8, reallocated=false
[DEBUG] RENDER: buffer 'if'

[DEBUG] Key received: Space
[DEBUG] InsertChar ' ': before len=2, cap=8
[DEBUG]   after len=3, cap=8
[DEBUG] RENDER: buffer 'if '

... (continues for each character)

Final after typing "if x > 0:"
[DEBUG] RENDER: buffer 'if x > 0:'
```

#### Press Enter:
```
[DEBUG] Key received: Enter
[DEBUG] AcceptLine
[DEBUG]   Line ends with ':', entering multi-line mode
[DEBUG]   in_multiline = true
[DEBUG]   lines = ["if x > 0:"]
[DEBUG]   buffer cleared, cursor = 0
[DEBUG] RENDER: prompt '... ', buffer ''
```

---

### Line 2: Press Tab, type "if y > 0:"

#### Tab for indent:
```
[DEBUG] Key received: Tab
[DEBUG] InsertIndent: before len=0, cap=0
[DEBUG]   after len=4, cap=8, reallocated=true
[DEBUG] RENDER: buffer '    '
```

#### Type "if y > 0:":
```
[DEBUG] InsertChar 'i': buffer '    i'
[DEBUG] InsertChar 'f': buffer '    if'
[DEBUG] InsertChar ' ': buffer '    if '
... (each character)

Final:
[DEBUG] RENDER: buffer '    if y > 0:'
```

#### Press Enter:
```
[DEBUG] Key received: Enter
[DEBUG] AcceptLine
[DEBUG]   Line ends with ':', entering multi-line mode
[DEBUG]   in_multiline = true
[DEBUG]   lines = ["if x > 0:", "    if y > 0:"]
[DEBUG]   buffer cleared, cursor = 0
[DEBUG] RENDER: prompt '... ', buffer ''
```

---

### Line 3: Press Tab twice, type "print(...)"

#### First Tab:
```
[DEBUG] Key received: Tab
[DEBUG] InsertIndent: before len=0, cap=0
[DEBUG]   after len=4, cap=8
[DEBUG] RENDER: buffer '    '
```

#### Second Tab:
```
[DEBUG] Key received: Tab
[DEBUG] InsertIndent: before len=4, cap=8
[DEBUG]   after len=8, cap=8
[DEBUG] RENDER: buffer '        '  (8 spaces = 2 indent levels)
```

#### Type 'print("both positive")':
```
[DEBUG] InsertChar 'p': buffer '        p'
... (each character)

Final:
[DEBUG] RENDER: buffer '        print("both positive")'
```

#### Press Enter:
```
[DEBUG] Key received: Enter
[DEBUG] AcceptLine
[DEBUG]   Line does NOT end with ':'
[DEBUG]   No unbalanced brackets
[DEBUG]   Complete input!
[DEBUG]   lines = ["if x > 0:", "    if y > 0:", '        print("both positive")']
[DEBUG]   Full input = "if x > 0:\n    if y > 0:\n        print(\"both positive\")"
[DEBUG]   Executing code...
```

---

## What You Should See (With Backspace Testing)

### If you press Backspace after Tab:

#### Scenario: Tab then Backspace
```
[DEBUG] Key received: Tab
[DEBUG] InsertIndent: buffer '    '
[DEBUG] RENDER: buffer '    ', cursor at column 8

[DEBUG] Key received: Backspace
[DEBUG] Backspace: cursor=4, buffer='    ', len=4
[DEBUG]   before_cursor='    '
[DEBUG]   In leading whitespace: deleting 4 spaces
[DEBUG]   has_content_after=false, would_be_empty=true
[DEBUG]   Would be empty, deleting only 1 space
[DEBUG]   After deletion: buffer='   ', cursor=3
[DEBUG] RENDER: buffer '   ', cursor at column 7
```

---

## Full Session Example

```
>>> if x > 0:
...     if y > 0:
...         print("both positive")
```

### Buffer State Timeline

| Line | Prompt | Buffer Content | Cursor | In Multi-line? |
|------|--------|----------------|--------|----------------|
| 1 | `>>>` | `'if x > 0:'` | 10 | NO (becoming YES) |
| 1 (after Enter) | `...` | `''` | 0 | YES |
| 2 | `...` | `'    if y > 0:'` | 14 | YES |
| 2 (after Enter) | `...` | `''` | 0 | YES |
| 3 | `...` | `'        print("both positive")'` | 32 | YES |
| 3 (after Enter) | Executing... | - | - | NO (complete) |

---

## To Capture YOUR Actual Session

Run this to see exactly what happened:

```bash
# Run with debug logging
TUI_DEBUG=1 ./target/debug/simple --tui 2> my_if_statements.log

# (Type your if statements)
# Press Ctrl+D to exit

# View the log
cat my_if_statements.log
```

Or filter for specific events:
```bash
# See only key presses and buffer state
grep -E "Key received|buffer=" my_if_statements.log

# See whitespace checks
grep -E "before_cursor|leading whitespace|would_be_empty" my_if_statements.log
```
