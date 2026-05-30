# TUI Multiline Mode Exit Logic Fix

## Problem Reported

When entering nested blocks in TUI mode:
```
>>> if 1:
...     if 1:
...         print 1
```

**Issue**: After entering "print 1" (which doesn't end with ':'), the REPL exited multiline mode and executed, when it should have stayed in multiline mode waiting for more input or an empty line.

**Expected Python REPL behavior**:
- When in multiline mode, non-empty lines should keep you in multiline mode
- Only an empty line should exit multiline mode and execute the block

## Root Cause

**Location**: `src/driver/src/cli/tui/editor.rs` lines 276-299 (old code)

**Problem**:
```rust
if line.trim_end().ends_with(':') || self.has_unbalanced_brackets() {
    // Enter multiline mode
    self.in_multiline = true;
    // ...
} else {
    // ❌ Exit multiline and execute - WRONG when already in multiline!
    let full_input = self.lines.join("\n");
    self.reset();
    EditorResult::Accepted(full_input)
}
```

The logic only checked:
1. Does line end with ':'?
2. Are there unbalanced brackets?

But it didn't check: **Are we already in multiline mode?**

This caused:
- Line 1: "if 1:" → Enters multiline ✅
- Line 2: "    if 1:" → Stays in multiline ✅
- Line 3: "        print 1" → Exits and executes ❌ (should stay!)

## Fix Implementation

### New Logic with Three Cases

**Modified Code** (lines 272-330):
```rust
EditorAction::AcceptLine => {
    let line = self.buffer.clone();
    self.lines.push(line.clone());

    // Case 1: Line ends with ':' or has unbalanced brackets
    if line.trim_end().ends_with(':') || self.has_unbalanced_brackets() {
        // Enter/stay in multiline mode
        self.in_multiline = true;
        let auto_indent = self.calculate_auto_indent(&line);
        self.buffer = auto_indent;
        self.cursor = self.buffer.len();
        EditorResult::Continue
    }
    // Case 2: Already in multiline mode
    else if self.in_multiline {
        if line.trim().is_empty() {
            // ✅ Empty line - complete the block and execute
            let full_input = self.lines.join("\n");
            self.reset();
            EditorResult::Accepted(full_input)
        } else {
            // ✅ Non-empty line - stay in multiline mode
            let auto_indent = self.calculate_auto_indent(&line);
            self.buffer = auto_indent;
            self.cursor = self.buffer.len();
            EditorResult::Continue
        }
    }
    // Case 3: Single line complete
    else {
        let full_input = self.lines.join("\n");
        self.reset();
        EditorResult::Accepted(full_input)
    }
}
```

### Key Changes

1. **Added `else if self.in_multiline` branch** - Checks if we're already in multiline mode
2. **Empty line detection** - `line.trim().is_empty()` triggers execution
3. **Non-empty line stays** - Continues multiline mode with auto-indent

## Behavior Changes

### Before Fix

```
>>> if 1:
...     if 1:
...         print 1
ERROR: Executed too early!
```

- After "print 1" + Enter → Immediately executed (wrong!)
- No way to add more lines to the block

### After Fix

```
>>> if 1:
...     if 1:
...         print 1
...         ▎               ← Stays in multiline, ready for more
```

Press Enter again (empty line):
```
>>> if 1:
...     if 1:
...         print 1
...
[Executes the complete block]
```

### Test Case

**Input sequence**:
1. "if 1:" + Enter → Multiline mode, 4 spaces indent
2. "    if 1:" + Enter → Stay in multiline, 8 spaces indent
3. "        print 1" + Enter → **Stay in multiline** (NEW!), 8 spaces indent
4. Enter (empty line) → Execute block

**Result**: Matches Python REPL behavior exactly!

## Test Results

### New Test: `test_multiline_stays_active_on_non_colon_line`

```
After 'if 1:' + Enter:
  result: Continue
  in_multiline: true
  buffer: '    '

After '    if 1:' + Enter:
  result: Continue
  in_multiline: true
  buffer: '        '

After '        print 1' + Enter:
  result: Continue          ← Stays in multiline! ✅
  in_multiline: true
  buffer: '        '

After empty line + Enter:
  result: Accepted("if 1:\n    if 1:\n        print 1\n        ")
  in_multiline: false

✅ PASS: Multiline mode stays active correctly!
```

### All Tests Pass

```
running 10 tests
test cli::tui::editor::tests::test_auto_indentation_after_colon ... ok
test cli::tui::editor::tests::test_backspace_after_text_deletes_one_char ... ok
test cli::tui::editor::tests::test_backspace_deletes_4_spaces_with_text_after ... ok
test cli::tui::editor::tests::test_backspace_deletes_full_indent_with_prevention ... ok
test cli::tui::editor::tests::test_backspace_deletes_partial_indent_with_prevention ... ok
test cli::tui::editor::tests::test_cursor_movement ... ok
test cli::tui::editor::tests::test_insert_char ... ok
test cli::tui::editor::tests::test_insert_indent ... ok
test cli::tui::editor::tests::test_multiline_stays_active_on_non_colon_line ... ok
test cli::tui::editor::tests::test_nested_auto_indentation ... ok

test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured
```

## Files Modified

- `src/driver/src/cli/tui/editor.rs`
  - Modified `AcceptLine` handler (lines 272-330)
  - Added `test_multiline_stays_active_on_non_colon_line` test (lines 599-662)

## Verification

### Manual Testing

```bash
./target/debug/simple --tui
```

**Test Scenario**:
```
>>> if 1:
...     if 1:
...         print 1
...                     ← Press Enter here, should stay in multiline
```

**Expected**: Cursor stays at "... " with 8 spaces, ready for more input

**To execute**: Press Enter on an empty line

## Comparison with Python REPL

### Python Behavior
```python
>>> if True:
...     if True:
...         print(1)
...                     # Still waiting for input
```

Press Enter on empty line → Executes

### Simple TUI Behavior (After Fix)
```
>>> if 1:
...     if 1:
...         print 1
...                     # Still waiting for input ✅
```

Press Enter on empty line → Executes ✅

**Result**: Matches Python REPL behavior exactly!

## Impact

- ✅ Python-like multiline block entry
- ✅ Can build complex nested structures
- ✅ Empty line exits multiline mode
- ✅ Consistent with Python REPL UX
- ✅ No breaking changes to existing functionality

## Related Work

This fix complements previous TUI improvements:
- Auto-indentation (from `TUI_INDENTATION_BUG_FIX.md`)
- Rendering fixes (no duplicate line drawing)
- Smart backspace (4-space deletion)
- Empty buffer prevention

See also:
- `TUI_INDENTATION_BUG_FIX.md` - Auto-indent and rendering fixes
- `TUI_NORMAL_MODE_COMPARISON.md` - Mode comparison
- `test_tui_indent_fix.md` - Manual testing guide
