# TUI Visibility Test - Manual Testing Guide

## Fixes Implemented

### Fix 1: Show Last Line After Enter
**Problem:** When you pressed Enter, the line disappeared before you could see it.
**Solution:** Now shows the completed line before moving to the next line.

### Fix 2: Make Indentation Visible
**Problem:** Spaces were invisible, so you couldn't see indentation.
**Solution:** Leading spaces are now shown as middle dots (·).

---

## Manual Test Instructions

### Test 1: Single Line Entry
```bash
./target/debug/simple --tui
```

1. Type: `x = 42`
2. Press Enter
3. **EXPECTED:** You should see `>>> x = 42` before moving to next prompt
4. **BEFORE FIX:** Line would disappear immediately

### Test 2: Visible Indentation
```bash
./target/debug/simple --tui
```

1. Type: `if x > 0:`
2. Press Enter (enters multi-line mode)
3. Press Tab
4. **EXPECTED:** You should see `... ····` (4 middle dots showing 4 spaces)
5. **BEFORE FIX:** Just `... ` with invisible spaces

### Test 3: Two If Statements (Complete Scenario)
```bash
./target/debug/simple --tui
```

**Step-by-step:**
```
>>> if x > 0:↵        # Press Enter
... ····if y > 0:↵    # Tab, type "if y > 0:", Press Enter
... ········          # Tab, Tab (8 spaces = 8 dots)
```

**EXPECTED:**
- After first Enter: Line `>>> if x > 0:` stays visible
- After Tab: See `... ····` (4 dots)
- After second Enter: Line `... ····if y > 0:` stays visible
- After Tab Tab: See `... ········` (8 dots)

**BEFORE FIX:**
- Lines would disappear immediately
- Spaces were invisible (couldn't tell how many)

---

## Visual Examples

### Before Fixes
```
>>> if x > 0:
...                    ← Can't see what you typed!
...                    ← Can't see indent! Is it 4 spaces? 8?
```

### After Fixes
```
>>> if x > 0:↵
... ····if y > 0:↵     ← Can see the line AND the indent!
... ········           ← Can see 8 spaces = 8 dots
```

---

## What the Dots Mean

- `·` = One space
- `····` = 4 spaces (one Tab)
- `········` = 8 spaces (two Tabs)
- `············` = 12 spaces (three Tabs)

**Note:** Only **leading** spaces (indentation) are shown as dots. Spaces inside text remain normal spaces.

Example:
```
... ····if x > 0:          ← 4 dots at start, normal space after "x"
... ········print("hi")    ← 8 dots at start, normal space in "print("
```

---

## Exit Test

Press `Ctrl+D` to exit cleanly.

---

## Quick Verification

Run this complete sequence:
```bash
./target/debug/simple --tui

# Type exactly:
if x > 0:↵
    if y > 0:↵
        print("done")↵
↵
```

**EXPECTED OUTPUT:**
```
>>> if x > 0:
... ····if y > 0:
... ········print("done")
...
(execution output)
```

Each line should:
1. ✅ Stay visible after you press Enter
2. ✅ Show dots for leading spaces
3. ✅ Show normal text for code

---

## Comparing to Normal Mode

Normal mode (no `--tui` flag) does NOT have these features:
```bash
./target/debug/simple     # Normal mode
```

- Lines are visible (handled by rustyline)
- Spaces are still invisible
- No smart backspace

Only TUI mode (`--tui`) has:
- Visible indentation (dots)
- Smart backspace (delete 4 spaces)
- Empty buffer prevention
