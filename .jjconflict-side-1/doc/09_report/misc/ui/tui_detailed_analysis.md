# TUI REPL Detailed Analysis - Complete Log Breakdown

**Date:** 2025-12-27
**Log File:** `tui_debug_log.txt`
**Purpose:** Show exact flow of input characters, buffer state, and whitespace checking

---

## Test 1: Tab Inserts 4 Spaces

### Input Character Received
```
[DEBUG] Key received: Tab
```
**User pressed:** Tab key (byte: `\t` = 0x09)

### Buffer Before Insertion
```
[DEBUG] InsertIndent: before len=0, cap=0
```
- **Buffer:** `""` (empty)
- **Length:** 0 bytes
- **Capacity:** 0 bytes (no allocation yet)
- **Cursor:** 0 (at start)

### Buffer After Insertion
```
[DEBUG]   after len=4, cap=8, reallocated=true
```
- **Buffer:** `"    "` (4 spaces inserted)
- **Length:** 4 bytes
- **Capacity:** 8 bytes (String doubled from 0 → 8)
- **Cursor:** 4 (at end of 4 spaces)
- **Reallocation:** YES (capacity grew)

### Line Refresh
```
[DEBUG] RENDER: Clearing line, redrawing prompt + buffer '    '
[DEBUG] RENDER: Complete, cursor at column 8
```

**What was drawn:**
1. Clear entire current line
2. Render prompt: `">>> "` (green colored, NOT in buffer)
3. Render buffer: `"    "` (4 spaces)
4. Move cursor to column 8:
   - Prompt `">>> "` = 4 characters (columns 0-3)
   - Buffer `"    "` = 4 characters (columns 4-7)
   - Cursor at column 8 (after last space)

**Screen appearance:**
```
>>> ____
        ↑ cursor here (column 8)
    ↑↑↑↑ buffer (4 spaces)
↑↑↑↑ prompt (NOT in buffer)
```

---

## Test 2: Backspace Deletes Indent (Empty Buffer Prevention)

### Input Character Received
```
[DEBUG] Key received: Backspace
```
**User pressed:** Backspace key (byte: `\x7f` = 0x7F = 127)

### Buffer State When Backspace Pressed
```
[DEBUG] Backspace: cursor=4, buffer='    ', len=4, cap=8
```
- **Full Buffer:** `"    "` (4 spaces)
- **Cursor Position:** 4 (at end)
- **Length:** 4 bytes
- **Capacity:** 8 bytes

### Whitespace Check - before_cursor
```
[DEBUG]   before_cursor='    '
```

**What is checked:**
```rust
let before_cursor = &self.buffer[..self.cursor];
// before_cursor = &"    "[..4] = "    "
```

- **before_cursor:** `"    "` (slice from buffer start to cursor)
- **Check:** `before_cursor.chars().all(|c| c == ' ')`
- **Result:** ✅ TRUE (all 4 characters are spaces)

### Whitespace Detection Logic
```
[DEBUG]   In leading whitespace: deleting 4 spaces
```

**Logic executed:**
1. All characters before cursor are spaces → ✅ Leading whitespace
2. Calculate normal deletion: `spaces_to_delete = 4` (at least 4 spaces available)

### Empty Buffer Prevention Check
```
[DEBUG]   has_content_after=false, would_be_empty=true
```

**Logic:**
```rust
let has_content_after = self.cursor < self.buffer.len();
// has_content_after = 4 < 4 = false (cursor at end, no content after)

let would_be_empty = !has_content_after && self.buffer.len() == spaces_to_delete;
// would_be_empty = !false && 4 == 4 = true && true = true
```

- **has_content_after:** `false` (cursor=4, buffer.len()=4, nothing after cursor)
- **would_be_empty:** `true` (deleting 4 spaces from 4-byte buffer = empty)

### Override Decision
```
[DEBUG]   Would be empty, deleting only 1 space
```

**Decision:**
- Normal: Delete 4 spaces → buffer becomes `""`
- **Override:** Delete only 1 space → buffer becomes `"   "`
- **Reason:** Prevent empty buffer

### Buffer After Deletion
```
[DEBUG]   After deletion: cursor=3, buffer='   ', len=3, cap=8, reallocated=false
```

- **Buffer:** `"   "` (3 spaces remaining)
- **Cursor:** 3 (moved back 1 position)
- **Length:** 3 bytes
- **Capacity:** 8 bytes (unchanged)
- **Reallocation:** NO (in-place modification)

### Line Refresh
```
[DEBUG] RENDER: Clearing line, redrawing prompt + buffer '   '
[DEBUG] RENDER: Complete, cursor at column 7
```

**What was drawn:**
1. Clear entire current line
2. Render prompt: `">>> "`
3. Render buffer: `"   "` (3 spaces)
4. Move cursor to column 7:
   - Prompt = 4 characters (columns 0-3)
   - Buffer = 3 characters (columns 4-6)
   - Cursor at column 7 (after last space)

**Screen appearance:**
```
>>> ___
       ↑ cursor here (column 7)
    ↑↑↑ buffer (3 spaces)
↑↑↑↑ prompt
```

---

## Test 3: Tab + Text + Backspace (Normal 1-Char Delete)

### Initial State After Tab
- **Buffer:** `"       "` (7 spaces from previous test + another tab)

### Typing 'h'
```
[DEBUG] InsertChar 'h': before len=7, cap=8
[DEBUG]   after len=8, cap=8, reallocated=false
```

- **Before:** Buffer = `"       "` (7 spaces), cursor = 7
- **After:** Buffer = `"       h"` (7 spaces + 'h'), cursor = 8
- **Reallocation:** NO (capacity sufficient)

### Typing 'e'
```
[DEBUG] InsertChar 'e': before len=8, cap=8
[DEBUG]   after len=9, cap=16, reallocated=true
```

- **Before:** Buffer = `"       h"` (8 chars), cursor = 8
- **After:** Buffer = `"       he"` (9 chars), cursor = 9
- **Reallocation:** YES (capacity doubled 8 → 16)

### Typing 'l', 'l', 'o' (similar pattern)
Final buffer: `"       hello"` (7 spaces + "hello")

### Backspace After Typing Text
```
[DEBUG] Key received: Backspace
[DEBUG] Backspace: cursor=12, buffer='       hello', len=12, cap=16
[DEBUG]   before_cursor='       hello'
```

### Whitespace Check
```
[DEBUG]   Not in leading whitespace: deleting 1 char
```

**Logic:**
```rust
let before_cursor = &"       hello"[..12] = "       hello"
before_cursor.chars().all(|c| c == ' ') → false (has 'hello')
```

- **before_cursor:** `"       hello"` (7 spaces + "hello")
- **Check:** All spaces? → ❌ FALSE (contains text)
- **Result:** NOT in leading whitespace

### Normal Single-Character Deletion
- **Deleted:** 'o' (last character)
- **Buffer after:** `"       hell"`
- **Cursor after:** 11

---

## Summary Table

| Event | Input Byte | Buffer Before | Cursor Before | Whitespace? | Check Result | Buffer After | Cursor After |
|-------|-----------|---------------|---------------|-------------|--------------|--------------|--------------|
| Tab | `\t` (0x09) | `""` | 0 | N/A | Insert 4 spaces | `"    "` | 4 |
| Backspace | `\x7f` (127) | `"    "` | 4 | YES (all spaces) | `would_be_empty=true` | `"   "` | 3 |
| Type 'h' | `'h'` (104) | `"       "` | 7 | N/A | Insert char | `"       h"` | 8 |
| Type 'e' | `'e'` (101) | `"       h"` | 8 | N/A | Insert char | `"       he"` | 9 |
| Backspace | `\x7f` (127) | `"       hello"` | 12 | NO (has text) | Delete 1 char | `"       hell"` | 11 |

---

## Key Observations

### 1. **Prompt is NOT in Buffer**
- Prompt (`">>> "`) rendered separately
- Buffer starts at position 0 (after prompt visually)
- Cursor column = prompt.len() + buffer cursor position

### 2. **Whitespace Check Uses before_cursor**
```rust
let before_cursor = &self.buffer[..self.cursor];  // From start to cursor
if before_cursor.chars().all(|c| c == ' ') { ... }  // Check all spaces
```
- Checks from **buffer start to cursor**, NOT entire buffer
- Does NOT include prompt characters

### 3. **Empty Buffer Prevention**
```rust
let has_content_after = self.cursor < self.buffer.len();
let would_be_empty = !has_content_after && self.buffer.len() == spaces_to_delete;
```
- Detects when deletion would empty buffer completely
- Overrides normal 4-space deletion to delete only 1 space

### 4. **Line Refresh Always Complete**
- Clears entire line
- Redraws prompt + buffer from scratch
- Positions cursor correctly
- Atomic update (no flicker)

---

## File Location

**Full log:** `tui_debug_log.txt` (in project root)
**View with:** `cat tui_debug_log.txt` or `less tui_debug_log.txt`
