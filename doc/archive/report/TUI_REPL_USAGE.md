# TUI REPL - Quick Start Guide

## Building with TUI Support

```bash
# Build the Simple interpreter with TUI feature
cargo build --release --features tui

# Or for development
cargo build --features tui
```

## Using the TUI REPL

```bash
# Start TUI REPL (with smart backspace)
./target/debug/simple --tui

# Or with release build
./target/release/simple --tui
```

## Smart Backspace Demonstration

```
Simple Language v0.1.0 - Interactive Mode (TUI)
Using TUI mode with smart indentation:
  - Tab: Insert 4 spaces
  - Backspace: Delete indent (4 spaces) or 1 character
  - Ctrl+U: Delete indent or to start of line
  - Ctrl+C: Cancel input
  - Ctrl+D: Exit

>>> [Press Tab]
>>>     ____  ← 4 spaces inserted
>>> [Press Backspace]
>>>  ← All 4 spaces deleted at once! ✅

>>> [Press Tab]hello
>>>     ____hello  ← 4 spaces + text
>>> [Press Backspace]
>>>     ____hell  ← Only 'o' deleted (1 char) ✅
```

## Keybindings

| Key | Action |
|-----|--------|
| **Tab** | Insert 4 spaces |
| **Backspace** | Delete 4 spaces (if in leading whitespace) OR delete 1 character |
| **Delete** | Delete character after cursor |
| **Ctrl+U** | Delete indent or to start of line |
| **Ctrl+C** | Cancel current input |
| **Ctrl+D** | Exit REPL |
| **Enter** | Accept line (or continue multi-line) |
| **←→** | Move cursor left/right |
| **Home/End** | Jump to start/end of line |

## Comparison with Default REPL

| Feature | Default (rustyline) | TUI Mode |
|---------|---------------------|----------|
| **Backspace deletes 4 spaces** | ❌ No (limitation) | ✅ **Yes** |
| Tab inserts 4 spaces | ✅ Yes | ✅ Yes |
| Ctrl+U dedent | ⚠️ Limited | ✅ Full |
| Multi-line support | ✅ Yes | ✅ Yes |
| History | ✅ Yes | ⬜ TODO |
| Completion | ✅ Yes | ⬜ TODO |

## Why Use TUI Mode?

**Problem with default REPL:**
```python
>>> [Tab]      # Inserts 4 spaces
>>>     ____
>>> [Backspace]  # Only deletes 1 space ❌
>>>    ___       # Have to press 4 times
>>>   __
>>>  _
>>>
```

**Solution with TUI mode:**
```python
>>> [Tab]      # Inserts 4 spaces
>>>     ____
>>> [Backspace]  # Deletes all 4 spaces at once! ✅
>>>
```

## Environment Variable (Alternative)

You can also set an environment variable:

```bash
export SIMPLE_REPL_MODE=tui
./target/debug/simple  # Will use TUI mode
```

*Note: This feature is not implemented yet, but planned for future release.*

## Troubleshooting

### Error: "--tui flag requires the 'tui' feature"

**Solution:** Rebuild with TUI feature enabled:
```bash
cargo build --features tui
```

### Terminal looks broken after exit

**Solution:** Reset terminal:
```bash
reset
```

Or press Ctrl+D properly to exit (TUI cleans up terminal state).

## Technical Details

- **Backend:** crossterm (de-facto Rust TUI standard)
- **Framework:** ratatui (modern TUI framework)
- **Feature Flag:** `tui` (optional compilation)
- **Dependencies:** +150 KB binary size

## More Information

- Full documentation: `doc/features/TUI_REPL.md`
- Implementation report: `doc/report/TUI_REPL_IMPLEMENTATION_2025-12-27.md`
- Test code: `src/driver/src/cli/tui/editor.rs` (see unit tests)

---

**Enjoy smart indentation with the TUI REPL!** 🎉
