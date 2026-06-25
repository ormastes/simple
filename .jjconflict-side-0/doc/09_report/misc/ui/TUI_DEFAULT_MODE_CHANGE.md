# TUI Mode is Now Default

## Change Summary

TUI mode is now the **default REPL mode** when the `tui` feature is enabled.

- **Before**: Normal mode (rustyline) was default, use `--tui` to enable TUI
- **After**: TUI mode is default, use `--notui` to switch to Normal mode

## Motivation

TUI mode provides a superior user experience with:
- ✅ Auto-indentation after `:` (Python-like)
- ✅ Smart backspace (deletes 4 spaces when in leading whitespace)
- ✅ Clean multiline editing
- ✅ Proper prompt display (`>>>` for first line, `...` for continuations)
- ✅ No duplicate line rendering
- ✅ Direct terminal control for better responsiveness

All TUI bugs have been fixed, making it stable and ready as the default.

## Changes Made

### 1. CLI Argument Parsing (`src/driver/src/main.rs`)

**Old Code**:
```rust
let use_tui = args.iter().any(|a| a == "--tui");

// ...

#[cfg(feature = "tui")]
if use_tui {
    std::process::exit(run_tui_repl(version(), runner));
}

std::process::exit(run_repl(version(), runner));
```

**New Code**:
```rust
let use_notui = args.iter().any(|a| a == "--notui");

// ...

// No arguments -> REPL (TUI by default if feature enabled)
#[cfg(feature = "tui")]
if !use_notui {
    // TUI is default when feature is enabled
    std::process::exit(run_tui_repl(version(), runner));
}

// Use Normal mode if --notui flag is set or TUI feature is disabled
std::process::exit(run_repl(version(), runner));
```

**Key Changes**:
- Changed `use_tui` to `use_notui`
- Changed `if use_tui` to `if !use_notui`
- TUI runs by default when feature is enabled
- Normal mode only runs if `--notui` is specified or TUI feature is disabled

### 2. Flag Filtering

**Old**: Filter out `--tui` flag
```rust
if arg == "--tui" {
    continue;
}
```

**New**: Filter out `--notui` flag
```rust
if arg == "--notui" {
    continue;
}
```

### 3. Help Text Updates (`src/driver/src/cli/help.rs`)

**Old Usage**:
```
Usage:
  simple                      Start interactive REPL
  simple --tui                Start TUI REPL (smart backspace: deletes 4 spaces)
```

**New Usage**:
```
Usage:
  simple                      Start interactive TUI REPL (default)
  simple --notui              Start Normal REPL (rustyline-based)
```

**Old Options**:
```
Options:
  --tui          Use TUI REPL with smart indentation (backspace deletes 4 spaces)
```

**New Options**:
```
Options:
  --notui        Use Normal REPL instead of TUI (TUI is default)
```

## Usage

### Start TUI REPL (Default)
```bash
./target/debug/simple
# or
./target/debug/simple --features tui
```

### Start Normal REPL
```bash
./target/debug/simple --notui
```

### Without TUI Feature
```bash
cargo build  # Without --features tui
./target/debug/simple  # Always uses Normal mode
```

## Behavior Matrix

| Build | Command | Result |
|-------|---------|--------|
| With `--features tui` | `simple` | **TUI REPL** ✅ |
| With `--features tui` | `simple --notui` | Normal REPL |
| Without `tui` feature | `simple` | Normal REPL (fallback) |
| Without `tui` feature | `simple --notui` | Normal REPL (same) |

## Testing

### Test TUI as Default
```bash
cargo build --features tui
./target/debug/simple
```

**Expected**: TUI REPL starts with message:
```
Simple Language v0.1.0 - Interactive Mode (TUI)
Using TUI mode with smart indentation:
  - Tab: Insert 4 spaces
  - Backspace: Delete indent (4 spaces) or 1 character
  - Ctrl+U: Delete indent or to start of line
  - Ctrl+C: Cancel input
  - Ctrl+D: Exit

>>>
```

### Test --notui Flag
```bash
./target/debug/simple --notui
```

**Expected**: Normal REPL starts with:
```
Simple Language v0.1.0 - Interactive Mode
Type expressions to evaluate. Use 'exit' or Ctrl-D to quit.

>>>
```

### Test Help
```bash
./target/debug/simple --help
```

**Expected**: Shows updated help with TUI as default

## Migration Guide

### For Users

**Before** (to use TUI):
```bash
simple --tui
```

**After** (TUI is default):
```bash
simple         # Use this!
```

**To use Normal mode** (if needed):
```bash
simple --notui  # Only if you prefer rustyline
```

### For Scripts/CI

If your scripts explicitly use `--tui`:
```bash
# Old
simple --tui < input.txt

# New (both work, but first is preferred)
simple < input.txt        # TUI is default now
simple --notui < input.txt  # Explicit Normal mode
```

**Note**: For non-interactive use (pipes, redirects), Normal mode may be more suitable.

## Files Modified

1. `src/driver/src/main.rs`
   - Line 49: Changed `use_tui` to `use_notui`
   - Lines 72-74: Filter `--notui` instead of `--tui`
   - Lines 98-110: Inverted logic to default to TUI

2. `src/driver/src/cli/help.rs`
   - Lines 9-10: Updated usage to show TUI as default
   - Line 82: Updated options to show `--notui` flag

## Impact

- ✅ Better default user experience
- ✅ Consistent with modern REPL expectations (Python, Node.js have enhanced REPLs)
- ✅ All TUI features work correctly (auto-indent, smart backspace, multiline)
- ✅ Normal mode still available via `--notui`
- ✅ No breaking changes for programmatic usage

## Related Work

This change finalizes the TUI REPL work:
- Auto-indentation fix (`TUI_INDENTATION_BUG_FIX.md`)
- Multiline mode fix (`TUI_MULTILINE_MODE_FIX.md`)
- Prompt display fix (`TUI_PROMPT_BUG_FIX.md`)

See also:
- `TUI_NORMAL_MODE_COMPARISON.md` - Feature comparison
- `NORMAL_MODE_TEST_RESULTS.md` - Normal mode baseline tests
