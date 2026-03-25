# TUI Visibility Fixes - Implementation Summary

**Date:** 2025-12-27
**Issue:** TUI REPL had two visibility problems

---

## Problems Identified

### Problem 1: Cannot See Last Line After Enter
**Symptom:** When user presses Enter, the typed line disappears before it can be seen.

**Root Cause:**
- In `src/driver/src/cli/tui/repl.rs` lines 76-80
- When `EditorResult::Accepted` or multi-line `EditorResult::Continue` occurred
- Code immediately printed `\r\n` and moved to next line
- Never rendered the completed line first

**User Impact:**
```
>>> if x > 0:
...            ← Where did my line go?!
```

### Problem 2: Cannot See Indent in Screen
**Symptom:** Spaces are invisible - user cannot see indentation.

**Root Cause:**
- Spaces are just empty space characters
- No visual indicator for indentation
- User cannot tell if they have 4, 8, or 12 spaces

**User Impact:**
```
>>> if x > 0:
...     if y > 0:     ← How many spaces? Can't tell!
...                   ← Is this indented? How much?
```

---

## Solutions Implemented

### Fix 1: Show Line Before Moving to Next

**File:** `src/driver/src/cli/tui/repl.rs`

**Change 1: Multi-line Entry (lines 73-86)**
```rust
EditorResult::Continue => {
    // Continue editing - check if we entered multi-line mode
    if editor.is_multiline() {
        // Show the line that was just completed before switching to ... prompt
        let last_line = editor.lines().last().map(|s| s.as_str()).unwrap_or("");
        let visible_line = make_indent_visible(last_line);
        let mut stdout = io::stdout();
        queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();
        queue!(stdout, SetForegroundColor(Color::Green), Print(">>> "), ResetColor).ok();
        queue!(stdout, Print(&visible_line), Print("\r\n")).ok();
        stdout.flush().ok();
        // Prompt will be updated to "... " on next loop iteration
    }
}
```

**Change 2: Complete Input (lines 88-99)**
```rust
EditorResult::Accepted(input) => {
    // Show the final line before moving to next line
    let last_line = input.lines().last().unwrap_or("");
    let visible_line = make_indent_visible(last_line);
    let mut stdout = io::stdout();
    queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();

    // Determine which prompt to show
    let line_prompt = if input.lines().count() > 1 { "... " } else { ">>> " };
    queue!(stdout, SetForegroundColor(Color::Green), Print(line_prompt), ResetColor).ok();
    queue!(stdout, Print(&visible_line), Print("\r\n")).ok();
    stdout.flush().ok();

    // ... then execute ...
}
```

**Effect:**
- Now shows the completed line before moving to next line
- User can see what they just typed

### Fix 2: Visible Indentation with Middle Dots

**File:** `src/driver/src/cli/tui/repl.rs`

**New Function (lines 156-177)**
```rust
/// Make indentation visible by replacing leading spaces with middle dots
fn make_indent_visible(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut in_leading_space = true;

    for ch in s.chars() {
        if in_leading_space {
            if ch == ' ' {
                // Replace space with middle dot (·)
                result.push('·');
            } else {
                // First non-space character
                in_leading_space = false;
                result.push(ch);
            }
        } else {
            result.push(ch);
        }
    }

    result
}
```

**Usage in Render (lines 171-174)**
```rust
// Print buffer with visible indentation
let buffer = editor.buffer();
let visible_buffer = make_indent_visible(buffer);
queue!(stdout, Print(&visible_buffer))?;
```

**Effect:**
- Leading spaces are shown as middle dots (·)
- Spaces inside text remain normal spaces
- User can clearly see indentation levels

---

## Visual Comparison

### Before Fixes
```
>>> if x > 0:
...                    ← Can't see what I typed!
...                    ← Can't see indent!
```

### After Fixes
```
>>> if x > 0:          ← Line stays visible! ✅
... ····if y > 0:      ← Can see 4-space indent! ✅
... ········           ← Can see 8-space indent! ✅
```

---

## Technical Details

### Middle Dot Character
- Unicode: U+00B7
- Character: `·`
- Display: Shows as a small centered dot
- Why: Clearly visible but not intrusive

### Algorithm
1. Iterate through string character by character
2. Track if we're still in leading spaces
3. Replace each leading space with `·`
4. Once we hit non-space, switch to normal rendering
5. All subsequent spaces remain normal

### Example Transformation
```
Input:  "    if y > 0:"
Output: "····if y > 0:"
         ^^^^
         Leading spaces → dots

Input:  "    print(\"hello world\")"
Output: "····print(\"hello world\")"
         ^^^^          ^
         Leading       Normal space
         spaces        (not leading)
```

---

## Files Modified

1. **`src/driver/src/cli/tui/repl.rs`**
   - Added `make_indent_visible()` function (20 lines)
   - Updated `EditorResult::Continue` handler (13 lines)
   - Updated `EditorResult::Accepted` handler (12 lines)
   - Updated `render_prompt()` to use visible buffer (3 lines)

**Total Changes:** ~50 lines added/modified

---

## Testing

### Manual Testing
See `test_tui_visibility.md` for manual test instructions.

### Key Test Cases
1. ✅ Single line entry - line stays visible
2. ✅ Multi-line entry - each line stays visible
3. ✅ Tab creates visible dots
4. ✅ Multiple tabs create multiple sets of dots
5. ✅ Dots only for leading spaces
6. ✅ Spaces in text remain normal

### Test Command
```bash
./target/debug/simple --tui

# Type:
if x > 0:↵
    if y > 0:↵
        print("done")↵
↵
```

**Expected:**
```
>>> if x > 0:
... ····if y > 0:
... ········print("done")
...
```

---

## Benefits

1. **Improved UX:** Users can see what they typed
2. **Clear Indentation:** No more guessing indent levels
3. **Debugging Aid:** Visual feedback for smart backspace
4. **Consistent:** Works for all TUI interactions

---

## Limitations

1. **TUI Mode Only:** Normal mode still has invisible spaces
2. **Leading Spaces Only:** Dots only show leading indentation
3. **Fixed Character:** Currently hardcoded to middle dot (·)

Future enhancement: Make the indicator character configurable.

---

## Backward Compatibility

- ✅ No breaking changes
- ✅ Only affects TUI mode (`--tui` flag)
- ✅ Normal mode unchanged
- ✅ Existing tests still pass

---

## Related Features

This fix complements:
- Smart backspace (delete 4 spaces)
- Empty buffer prevention
- Multi-line editing
- Debug logging (TUI_DEBUG=1)

Together, these create a Python-like REPL experience with clear visual feedback.
