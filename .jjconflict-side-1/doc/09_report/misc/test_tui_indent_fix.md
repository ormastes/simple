# Manual TUI Indentation Fix Test

## Test Setup

```bash
TUI_DEBUG=1 ./target/debug/simple --tui
```

## Test Case 1: Auto-Indentation After ':'

### Steps:
1. Type: `if x > 0:`
2. Press Enter

### Expected Result:
- Line "if x > 0:" should remain visible
- Next prompt should be `...     ` (with 4 spaces auto-indent)
- Cursor should be at column 8 (after "... " + 4 spaces)

### Debug Output Expected:
```
[DEBUG] AcceptLine: Entering multiline mode
[DEBUG]   Previous line: 'if x > 0:'
[DEBUG]   Auto-indent: 4 spaces
[DEBUG] RENDER: Clearing line, redrawing prompt + buffer '    '
[DEBUG] RENDER: Complete, cursor at column 8
```

## Test Case 2: Typing in Indented Line

### Steps:
1. Type: `if x > 0:`
2. Press Enter
3. Type: `print`

### Expected Result:
- First line: `>>> if x > 0:`
- Second line: `...     print` (text appears on CURRENT line, not previous)
- Each character should appear at the correct position

### Expected Behavior:
- After typing 'p': cursor at column 9
- After typing 'r': cursor at column 10
- After typing 'i': cursor at column 11
- After typing 'n': cursor at column 12
- After typing 't': cursor at column 13

## Test Case 3: Nested Indentation

### Steps:
1. Type: `if x > 0:`
2. Press Enter
3. Type: `if y > 0:`
4. Press Enter

### Expected Result:
- Line 1: `>>> if x > 0:`
- Line 2: `...     if y > 0:`
- Line 3: `...         ` (8 spaces: 4 from first if, 4 from second if)

### Debug Output Expected:
```
[DEBUG] AcceptLine: Entering multiline mode
[DEBUG]   Previous line: '    if y > 0:'
[DEBUG]   Auto-indent: 8 spaces
```

## Test Case 4: Backspace in Auto-Indent

### Steps:
1. Type: `if x > 0:`
2. Press Enter (now at auto-indent with 4 spaces)
3. Press Backspace

### Expected Result:
- All 4 spaces should be deleted (smart backspace)
- Buffer should become empty
- Cursor at column 4 (after "... ")

## Verification Checklist

- [ ] Auto-indent appears after pressing Enter following ':'
- [ ] Typed characters appear on current line, not previous line
- [ ] Nested indentation works (8 spaces after two levels)
- [ ] Smart backspace deletes full indent (4 spaces)
- [ ] Previous lines remain visible
- [ ] Cursor positioning is correct

## Notes

- The fix modifies `editor.rs` `AcceptLine` action
- Adds `calculate_auto_indent()` method
- Auto-indent is calculated based on existing indentation + 4 spaces if line ends with ':'
