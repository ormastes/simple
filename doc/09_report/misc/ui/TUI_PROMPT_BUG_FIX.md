# TUI Prompt Display Bug Fix

## Problem Reported

When entering nested if statements in TUI mode, the prompt incorrectly showed ">>>" for continuation lines instead of "...":

```
>>> if 1:
>>> if 1:        ← BUG: Should be "..." not ">>>"
...
```

**Expected behavior**:
```
>>> if 1:        ← First line uses ">>>"
...     if 1:    ← Continuation lines use "..."
...
```

## Root Cause

**Location**: `src/driver/src/cli/tui/repl.rs` line 84 (old code)

**Problem**:
```rust
EditorResult::Continue => {
    let current_line_count = editor.lines().len();
    if editor.is_multiline() && current_line_count > prev_line_count {
        let last_line = editor.lines().last().map(|s| s.as_str()).unwrap_or("");
        let mut stdout = io::stdout();
        queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();
        queue!(stdout, SetForegroundColor(Color::Green), Print(">>> "), ResetColor).ok();  // ❌ Always ">>>"!
        queue!(stdout, Print(last_line), Print("\r\n")).ok();
        stdout.flush().ok();
        prev_line_count = current_line_count;
    }
}
```

When a new line was added in multiline mode, the code **always** displayed the previous line with ">>> " prompt, regardless of whether it was the first line or a continuation line.

### Why This Happened

The rendering code runs when `current_line_count > prev_line_count` (a new line was added):
1. First "if 1:" + Enter → line_count = 1 → Renders ">>> if 1:" ✅
2. Second "    if 1:" + Enter → line_count = 2 → Renders ">>> if 1:" ❌ (should be "... if 1:")
3. Next prompt correctly shows "..."

## Fix Implementation

**Modified Code** (lines 85-87):
```rust
EditorResult::Continue => {
    let current_line_count = editor.lines().len();
    if editor.is_multiline() && current_line_count > prev_line_count {
        let last_line = editor.lines().last().map(|s| s.as_str()).unwrap_or("");
        let mut stdout = io::stdout();
        queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();

        // ✅ Use correct prompt: ">>>" for first line, "..." for continuation
        let line_prompt = if current_line_count == 1 { ">>> " } else { "... " };
        queue!(stdout, SetForegroundColor(Color::Green), Print(line_prompt), ResetColor).ok();
        queue!(stdout, Print(last_line), Print("\r\n")).ok();
        stdout.flush().ok();
        prev_line_count = current_line_count;
    }
}
```

### Key Change

Added conditional prompt selection:
- `current_line_count == 1` → Use ">>> " (first line)
- `current_line_count > 1` → Use "... " (continuation lines)

## Behavior Changes

### Before Fix

```
>>> if 1:
>>> if 1:        ← Wrong prompt
>>> print 1      ← Wrong prompt
...              ← Next prompt is correct but previous lines show wrong prompt
```

### After Fix

```
>>> if 1:        ← Correct: first line uses ">>>"
...     if 1:    ← Correct: continuation uses "..."
...         print 1  ← Correct: continuation uses "..."
...              ← Correct: waiting for input
```

## Visual Comparison

### Python REPL (Expected)
```python
>>> if True:
...     if True:
...         print(1)
...
```

### Simple TUI (Before Fix)
```
>>> if 1:
>>> if 1:        # Wrong!
>>> print 1      # Wrong!
...
```

### Simple TUI (After Fix)
```
>>> if 1:
...     if 1:    # Correct!
...         print 1  # Correct!
...
```

Now matches Python REPL behavior exactly! ✅

## Test Case

Created `src/driver/tests/tui_prompt_bug_test.rs` to reproduce the bug:
- Enters two if statements
- Checks that second line shows "..." not ">>>"
- Verifies prompt consistency

## Files Modified

- `src/driver/src/cli/tui/repl.rs`
  - Line 85-87: Added conditional prompt selection based on line count

## Impact

- ✅ Visual consistency with Python REPL
- ✅ Clear distinction between first line and continuations
- ✅ Improved user experience
- ✅ No functional changes, only visual fix

## Verification

### Manual Testing

```bash
./target/debug/simple --tui
```

**Test**:
1. Type: `if 1:`
2. Press Enter → Should show ">>> if 1:" then "..." prompt
3. Type: `    if 1:`
4. Press Enter → Should show "...     if 1:" (not ">>>     if 1:")

**Expected Output**:
```
>>> if 1:
...     if 1:
...
```

All prompts correctly use "..." for continuation lines!

## Related Work

This fix complements other TUI improvements:
- Auto-indentation (`TUI_INDENTATION_BUG_FIX.md`)
- Multiline mode logic (`TUI_MULTILINE_MODE_FIX.md`)
- Rendering optimization (no duplicate line drawing)

See also:
- `TUI_INDENTATION_BUG_FIX.md` - Auto-indent and rendering fixes
- `TUI_MULTILINE_MODE_FIX.md` - Multiline exit logic
- `TUI_NORMAL_MODE_COMPARISON.md` - Mode comparison
