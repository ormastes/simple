# TUI Mode vs Normal Mode

## Two Different REPL Modes

---

## TUI Mode (Our Smart Backspace Implementation)

### How to Run
```bash
./target/debug/simple --tui
```

### Features
- ✅ **Smart backspace:** Deletes 4 spaces in leading whitespace
- ✅ **Empty buffer prevention:** Won't delete all spaces when buffer would be empty
- ✅ **Crossterm-based:** Direct terminal control
- ✅ **Raw mode:** Immediate keyboard response
- ✅ **Debug logging:** `TUI_DEBUG=1` shows all key events
- ✅ **Multi-line prompt:** Changes to `...` for continuation lines
- ✅ **Tab inserts 4 spaces**
- ✅ **Ctrl+U deletes indent**

### Backspace Behavior
```
Buffer: "    " (4 spaces)
Press Backspace:
  → Normal: Delete all 4 spaces
  → TUI Mode: Delete only 1 space (prevent empty buffer)

Buffer: "        " (8 spaces)
Press Backspace:
  → Deletes 4 spaces (leaves 4)

Buffer: "    hello"
Cursor after "hello"
Press Backspace:
  → Deletes only 'o' (not in leading whitespace)
```

### Visual Example
```
>>> if x > 0:
...     if y > 0:
...         ← Smart indent, multi-line prompt
```

### Debug Output
```bash
TUI_DEBUG=1 ./target/debug/simple --tui 2> debug.log

# Shows:
[DEBUG] Key received: Backspace
[DEBUG] Backspace: cursor=4, buffer='    '
[DEBUG]   before_cursor='    '
[DEBUG]   In leading whitespace: deleting 4 spaces
[DEBUG]   would_be_empty=true
[DEBUG]   Would be empty, deleting only 1 space
```

---

## Normal Mode (Default, Rustyline-based)

### How to Run
```bash
./target/debug/simple          # Default
# or
./target/debug/simple --repl
```

### Features
- ❌ **NO smart backspace:** Backspace always deletes 1 character
- ❌ **NO empty buffer prevention**
- ✅ **Rustyline library:** Standard readline editing
- ✅ **History:** Up/down arrow for command history
- ✅ **Line editing:** Emacs-style keybindings
- ❌ **NO debug logging**
- ❌ **Single prompt:** Always `>>>`
- ✅ **Tab for completion** (if configured)

### Backspace Behavior
```
Buffer: "    " (4 spaces)
Press Backspace 4 times:
  → Deletes 1 space each time
  → "   " → "  " → " " → ""
  → Buffer CAN become empty
```

### Visual Example
```
>>> if x > 0:
>>>     if y > 0:
>>>         ← No prompt change, no smart indent
```

### No Debug Output
- Uses rustyline's internal handling
- No visibility into key processing

---

## Comparison Table

| Feature | TUI Mode (`--tui`) | Normal Mode (default) |
|---------|-------------------|----------------------|
| **Backspace in whitespace** | Deletes 4 spaces | Deletes 1 character |
| **Empty buffer prevention** | ✅ YES | ❌ NO |
| **Multi-line prompt** | `...` | `>>>` |
| **Debug logging** | ✅ YES (TUI_DEBUG=1) | ❌ NO |
| **Terminal library** | crossterm | rustyline |
| **Raw mode** | ✅ YES | ❌ NO |
| **Tab key** | Inserts 4 spaces | Completion (if enabled) |
| **Ctrl+U** | Delete indent | Delete line |
| **Command history** | ❌ Not implemented | ✅ YES (up/down) |
| **Line editing** | Basic | Full Emacs-style |

---

## Which Mode Are You Using?

### Check Your Session

**If you see this → TUI Mode:**
```
>>> if x > 0:
...     ← prompt changed to "..."
```

**If you see this → Normal Mode:**
```
>>> if x > 0:
>>>     ← prompt stays ">>>"
```

### Check Backspace Behavior

**TUI Mode:**
- Type Tab → 4 spaces appear
- Press Backspace → All spaces deleted at once (or 1 if would be empty)

**Normal Mode:**
- Type Tab → May trigger completion or insert tab
- Press Backspace → Deletes 1 character at a time

---

## When to Use Each Mode

### Use TUI Mode (`--tui`)
- ✅ You want Python-style smart indentation
- ✅ You want to see debug logging
- ✅ You're testing the smart backspace feature
- ✅ You prefer 4-space indent deletion

### Use Normal Mode (default)
- ✅ You want command history (up/down arrows)
- ✅ You want standard readline editing
- ✅ You prefer traditional REPL behavior
- ✅ You don't need smart backspace

---

## Your Previous Session

When you typed **two if statements**, if you ran:

```bash
./target/debug/simple --tui    # TUI mode (smart backspace)
```
- Buffer would show `"    "` and `"        "` after tabs
- Backspace would delete 4 spaces
- Empty buffer prevention would activate

```bash
./target/debug/simple          # Normal mode
```
- Each backspace deletes 1 character
- No smart indent behavior
- No debug logging available

---

## Files Location

All our work has been on **TUI mode**:
- `src/driver/src/cli/tui/editor.rs` - Smart backspace logic
- `src/driver/src/cli/tui/keybindings.rs` - TUI keybindings
- `src/driver/src/cli/tui/repl.rs` - TUI REPL loop

Normal mode uses:
- Rustyline library (external dependency)
- No custom backspace logic
