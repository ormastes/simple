# TUI Indentation Bug Fix Summary

## Bugs Reported

1. **Missing Auto-Indentation**: TUI indentation does not add indentation after pressing Enter following ':'
2. **Rendering Issue**: When typing keys in indentation area, text rewrites previous line instead of current line

## Root Cause Analysis

### Bug #1: Missing Auto-Indentation

**Location**: `src/driver/src/cli/tui/editor.rs` lines 272-288 (old code)

**Problem**:
```rust
if line.trim_end().ends_with(':') || self.has_unbalanced_brackets() {
    self.in_multiline = true;
    self.buffer.clear();  // ❌ Buffer cleared - no auto-indent!
    self.cursor = 0;
    EditorResult::Continue
}
```

When entering multiline mode, the buffer was cleared completely. This meant:
- No automatic indentation added
- User had to manually type spaces for indentation
- Not Python-like behavior

### Bug #2: Rendering Issue (Separate Root Cause)

**Location**: `src/driver/src/cli/tui/repl.rs` lines 73-84 (old code)

**Problem**:
```rust
EditorResult::Continue => {
    // Continue editing - check if we entered multi-line mode
    if editor.is_multiline() {  // ❌ This runs EVERY time while in multiline!
        // Show the line that was just completed before switching to ... prompt
        let last_line = editor.lines().last().map(|s| s.as_str()).unwrap_or("");
        let mut stdout = io::stdout();
        queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();
        queue!(stdout, SetForegroundColor(Color::Green), Print(">>> "), ResetColor).ok();
        queue!(stdout, Print(last_line), Print("\r\n")).ok();  // ❌ Prints previous line EVERY keystroke!
        stdout.flush().ok();
    }
}
```

The code executed EVERY TIME `Continue` was returned while in multiline mode:
1. After "if x > 0:" + Enter → Prints ">>> if x > 0:\r\n" (correct)
2. After typing 'p' → Prints ">>> if x > 0:\r\n" AGAIN (wrong!)
3. After typing 'r' → Prints ">>> if x > 0:\r\n" AGAIN (wrong!)

Result: Previous line was rewritten on every keystroke, causing screen flicker and wrong line rendering.

## Fix Implementation

### Fix #1: Calculate and Set Auto-Indent

**Modified File**: `src/driver/src/cli/tui/editor.rs`

**Modified Code** (lines 272-300):
```rust
EditorAction::AcceptLine => {
    let line = self.buffer.clone();
    self.lines.push(line.clone());

    // Check if we need continuation (ends with ':' or has unbalanced brackets)
    if line.trim_end().ends_with(':') || self.has_unbalanced_brackets() {
        self.in_multiline = true;

        // ✅ Calculate auto-indent level
        let auto_indent = self.calculate_auto_indent(&line);

        if self.debug_mode {
            eprintln!("[DEBUG] AcceptLine: Entering multiline mode");
            eprintln!("[DEBUG]   Previous line: '{}'", line);
            eprintln!("[DEBUG]   Auto-indent: {} spaces", auto_indent.len());
        }

        // ✅ Set buffer to auto-indent
        self.buffer = auto_indent;
        self.cursor = self.buffer.len();

        EditorResult::Continue
    } else {
        // Complete input
        let full_input = self.lines.join("\n");
        self.reset();
        EditorResult::Accepted(full_input)
    }
}
```

### New Method: calculate_auto_indent()

**Added to editor.rs** (lines 351-364):
```rust
/// Calculate automatic indentation level for next line
/// Returns a string of spaces for the appropriate indent level
fn calculate_auto_indent(&self, line: &str) -> String {
    // Get existing indentation from the line
    let existing_indent = line.chars().take_while(|&c| c == ' ').count();

    // If line ends with ':', add one more indent level (4 spaces)
    if line.trim_end().ends_with(':') {
        " ".repeat(existing_indent + 4)
    } else {
        // Keep same indent level
        " ".repeat(existing_indent)
    }
}
```

### Fix #2: Track Line Count to Prevent Duplicate Rendering

**Modified File**: `src/driver/src/cli/tui/repl.rs`

**Added State Variable** (line 53):
```rust
// Track previous line count to detect when we just entered multiline mode
let mut prev_line_count = 0;
```

**Modified EditorResult::Continue Handler** (lines 76-91):
```rust
EditorResult::Continue => {
    // Check if we JUST entered multiline mode (line count increased)
    let current_line_count = editor.lines().len();
    if editor.is_multiline() && current_line_count > prev_line_count {
        // ✅ Only show previous line when line count INCREASED
        let last_line = editor.lines().last().map(|s| s.as_str()).unwrap_or("");
        let mut stdout = io::stdout();
        queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();
        queue!(stdout, SetForegroundColor(Color::Green), Print(">>> "), ResetColor).ok();
        queue!(stdout, Print(last_line), Print("\r\n")).ok();
        stdout.flush().ok();
        // Update prev_line_count
        prev_line_count = current_line_count;
    }
}
```

**Reset Line Count on Accepted/Cancelled** (lines 116, 124):
```rust
EditorResult::Accepted(input) => {
    // ... execution code ...
    prev_line_count = 0;  // ✅ Reset when exiting multiline
}
EditorResult::Cancelled => {
    // ... cancel code ...
    prev_line_count = 0;  // ✅ Reset when cancelling
}
```

**Key Insight**: Only render the previous line when `lines.len()` increases, not on every keystroke.

## Behavior Changes

### Before Both Fixes

**Problem 1: No Auto-Indent**
```
>>> if x > 0:
...                          ← Empty, no auto-indent
```

**Problem 2: Previous Line Rewritten on Every Keystroke**
```
>>> if x > 0:                ← Original line
>>> if x > 0:                ← Rewritten when user types 'p'
>>> if x > 0:                ← Rewritten when user types 'r'
>>> if x > 0:                ← Rewritten when user types 'i'
... pri▎                     ← Current line (finally visible)
```

### After Both Fixes

**Fix 1: Auto-Indent Working**
```
>>> if x > 0:
...     ▎                    ← 4 spaces auto-indent, cursor at column 8
```

**Fix 2: No Duplicate Rendering**
```
>>> if x > 0:                ← Rendered once when Enter pressed
...     p▎                   ← Text appears on current line, no flicker
```

User continues typing 'r', 'i', 'n', 't':
```
>>> if x > 0:                ← Previous line stays stable
...     print▎               ← Only current line updates
```

### Nested Indentation

```
>>> if x > 0:
...     if y > 0:
...         ▎                ← 8 spaces (4 + 4), cursor at column 12
```

## Test Results

### Unit Tests

✅ `test_auto_indentation_after_colon` - **PASS**
```
Before Enter:
  buffer: 'if x > 0:'
  in_multiline: false

After Enter:
  result: Continue
  buffer: '    '              ← 4 spaces present
  buffer.len(): 4
  cursor: 4
  in_multiline: true
```

✅ `test_nested_auto_indentation` - **PASS**
```
After first Enter:
  buffer: '    '              ← 4 spaces
  buffer.len(): 4

After second Enter:
  buffer: '        '          ← 8 spaces (4 + 4)
  buffer.len(): 8
```

## Files Modified

### 1. `src/driver/src/cli/tui/editor.rs` (Fix #1: Auto-Indent)
   - Modified `AcceptLine` handler (lines 272-300)
   - Added `calculate_auto_indent()` method (lines 351-364)
   - Updated unit tests to reflect empty buffer prevention behavior (lines 407-434)
   - Added new unit tests for auto-indentation (lines 470-546)

### 2. `src/driver/src/cli/tui/repl.rs` (Fix #2: Rendering)
   - Added `prev_line_count` state tracking (line 53)
   - Modified `EditorResult::Continue` handler to only render on line count increase (lines 76-91)
   - Reset line count on `Accepted` and `Cancelled` (lines 116, 124)

## Verification

### Manual Testing

```bash
TUI_DEBUG=1 ./target/debug/simple --tui
```

**Test Scenario**:
1. Type: `if x > 0:`
2. Press Enter
3. Verify: Prompt shows `...     ` with 4 spaces
4. Type: `print("hello")`
5. Verify: Text appears on current line, correctly indented

**Expected Debug Output**:
```
[DEBUG] AcceptLine: Entering multiline mode
[DEBUG]   Previous line: 'if x > 0:'
[DEBUG]   Auto-indent: 4 spaces
[DEBUG] RENDER: Clearing line, redrawing prompt + buffer '    '
[DEBUG] RENDER: Complete, cursor at column 8
```

### Automated Tests

```bash
# Run auto-indentation tests
cargo test --features tui --bin simple test_auto_indentation -- --nocapture

# Run nested indentation test
cargo test --features tui --bin simple test_nested_auto_indentation -- --nocapture

# Run all TUI editor tests
cargo test --features tui --bin simple cli::tui::editor::tests
```

## Impact Assessment

### Positive Impact

- ✅ Python-like auto-indentation now works
- ✅ Improved user experience for multi-line input
- ✅ Consistent with Normal mode behavior (which has auto-indent from rustyline)
- ✅ Likely fixes rendering issue as side effect

### No Breaking Changes

- Existing functionality preserved
- Smart backspace still works with auto-indent
- Empty buffer prevention still works
- All existing tests still pass

## Related Work

This fix complements the previous TUI work:
- Smart backspace (deletes 4 spaces) - Still works
- Empty buffer prevention - Still works
- Line visibility after Enter - Fixed previously
- Multi-line mode detection - Works with auto-indent

See also:
- `TUI_NORMAL_MODE_COMPARISON.md` - Mode comparison
- `NORMAL_MODE_TEST_RESULTS.md` - Normal mode baseline
- `test_tui_indent_fix.md` - Manual testing guide

## Conclusion

✅ **Both bugs fixed** with two separate fixes:

### Bug #1: Missing Auto-Indentation
- **Root Cause**: Buffer cleared without adding indentation
- **Fix**: Calculate and set auto-indent based on previous line
- **Result**: Python-style auto-indentation now works

### Bug #2: Previous Line Rewritten
- **Root Cause**: Rendering code executed on every keystroke in multiline mode
- **Fix**: Track line count, only render when count increases
- **Result**: Previous lines remain stable, no flicker, clean rendering

### Impact

- ✅ TUI mode now has proper Python-style indentation
- ✅ Rendering is clean and efficient (no duplicate draws)
- ✅ User experience matches modern code editors
- ✅ All existing tests pass
- ✅ No breaking changes to existing functionality

The fixes bring TUI mode to feature parity with Normal mode's auto-indent behavior while providing a cleaner, more efficient rendering experience.
