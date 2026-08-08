# Debug Log: Two If Statements + Backspace

## Scenario: Type this, then press Backspace

```python
>>> if x > 0:
...     if y > 0:
...         ← BACKSPACE here
```

---

## Step-by-Step Debug Log

### Step 1: Type "if x > 0:" and press Enter

**Typing "if x > 0:"** (character by character)
```
[DEBUG] InsertChar 'i': buffer='i', cursor=1
[DEBUG] InsertChar 'f': buffer='if', cursor=2
[DEBUG] InsertChar ' ': buffer='if ', cursor=3
[DEBUG] InsertChar 'x': buffer='if x', cursor=4
[DEBUG] InsertChar ' ': buffer='if x ', cursor=5
[DEBUG] InsertChar '>': buffer='if x >', cursor=6
[DEBUG] InsertChar ' ': buffer='if x > ', cursor=7
[DEBUG] InsertChar '0': buffer='if x > 0', cursor=8
[DEBUG] InsertChar ':': buffer='if x > 0:', cursor=9
[DEBUG] RENDER: prompt='>>>', buffer='if x > 0:', cursor at column 13
```

**Press Enter:**
```
[DEBUG] Key received: Enter
[DEBUG] AcceptLine
[DEBUG]   Line ends with ':', entering multi-line mode
[DEBUG]   in_multiline = true
[DEBUG]   lines = ["if x > 0:"]
[DEBUG]   buffer cleared
[DEBUG]   cursor = 0
[DEBUG] RENDER: prompt='... ', buffer='', cursor at column 4
```

---

### Step 2: Press Tab for indent

```
[DEBUG] Key received: Tab
[DEBUG] InsertIndent: before len=0, cap=0
[DEBUG]   after len=4, cap=8, reallocated=true
[DEBUG] RENDER: prompt='... ', buffer='    ', cursor at column 8
```

**Buffer state:**
- Prompt: `"... "`
- Buffer: `"    "` (4 spaces)
- Cursor: 4 (at end of 4 spaces)
- Screen column: 8 (4 for prompt + 4 for buffer)

---

### Step 3: Type "if y > 0:" and press Enter

**Typing "if y > 0:"**
```
[DEBUG] InsertChar 'i': buffer='    i', cursor=5
[DEBUG] InsertChar 'f': buffer='    if', cursor=6
[DEBUG] InsertChar ' ': buffer='    if ', cursor=7
[DEBUG] InsertChar 'y': buffer='    if y', cursor=8
[DEBUG] InsertChar ' ': buffer='    if y ', cursor=9
[DEBUG] InsertChar '>': buffer='    if y >', cursor=10
[DEBUG] InsertChar ' ': buffer='    if y > ', cursor=11
[DEBUG] InsertChar '0': buffer='    if y > 0', cursor=12
[DEBUG] InsertChar ':': buffer='    if y > 0:', cursor=13
[DEBUG] RENDER: prompt='... ', buffer='    if y > 0:', cursor at column 17
```

**Press Enter:**
```
[DEBUG] Key received: Enter
[DEBUG] AcceptLine
[DEBUG]   Line ends with ':', entering multi-line mode
[DEBUG]   in_multiline = true
[DEBUG]   lines = ["if x > 0:", "    if y > 0:"]
[DEBUG]   buffer cleared
[DEBUG]   cursor = 0
[DEBUG] RENDER: prompt='... ', buffer='', cursor at column 4
```

---

### Step 4: Press Tab (first indent)

```
[DEBUG] Key received: Tab
[DEBUG] InsertIndent: before len=0, cap=0
[DEBUG]   after len=4, cap=8, reallocated=true
[DEBUG] RENDER: prompt='... ', buffer='    ', cursor at column 8
```

**Buffer state:**
- Buffer: `"    "` (4 spaces)
- Cursor: 4

---

### Step 5: Press Tab (second indent)

```
[DEBUG] Key received: Tab
[DEBUG] InsertIndent: before len=4, cap=8
[DEBUG]   after len=8, cap=8, reallocated=false
[DEBUG] RENDER: prompt='... ', buffer='        ', cursor at column 12
```

**Buffer state:**
- Buffer: `"        "` (8 spaces = 2 indent levels)
- Cursor: 8 (at end of 8 spaces)
- Screen column: 12 (4 for prompt + 8 for buffer)

---

### Step 6: **PRESS BACKSPACE** ← The key moment!

```
[DEBUG] Key received: Backspace
[DEBUG] Backspace: cursor=8, buffer='        ', len=8, cap=8
[DEBUG]   before_cursor='        '
[DEBUG]   In leading whitespace: deleting 4 spaces
[DEBUG]   has_content_after=false, would_be_empty=false
[DEBUG]   Proceeding with 4 space deletion
[DEBUG]   After deletion: cursor=4, buffer='    ', len=4, cap=8, reallocated=false
[DEBUG] RENDER: prompt='... ', buffer='    ', cursor at column 8
```

**What happened:**
- **Before:** buffer = `"        "` (8 spaces), cursor = 8
- **Check:** `before_cursor = "        "` (all spaces) ✓ Leading whitespace
- **Check:** `has_content_after = false` (cursor at end)
- **Check:** `would_be_empty = false` (8 spaces, deleting 4 leaves 4)
- **Action:** Delete 4 spaces (normal smart backspace)
- **After:** buffer = `"    "` (4 spaces), cursor = 4

---

### Step 7: Press Backspace AGAIN

```
[DEBUG] Key received: Backspace
[DEBUG] Backspace: cursor=4, buffer='    ', len=4, cap=8
[DEBUG]   before_cursor='    '
[DEBUG]   In leading whitespace: deleting 4 spaces
[DEBUG]   has_content_after=false, would_be_empty=true
[DEBUG]   Would be empty, deleting only 1 space
[DEBUG]   After deletion: cursor=3, buffer='   ', len=3, cap=8, reallocated=false
[DEBUG] RENDER: prompt='... ', buffer='   ', cursor at column 7
```

**What happened:**
- **Before:** buffer = `"    "` (4 spaces), cursor = 4
- **Check:** `before_cursor = "    "` (all spaces) ✓ Leading whitespace
- **Check:** `has_content_after = false` (cursor at end)
- **Check:** `would_be_empty = true` (4 spaces, deleting 4 = empty!) ⚠️
- **Action:** **Override!** Delete only 1 space (prevent empty buffer)
- **After:** buffer = `"   "` (3 spaces), cursor = 3

---

## Summary Table

| Step | Input | Buffer Before | Cursor | Leading WS? | would_be_empty? | Action | Buffer After | Cursor |
|------|-------|---------------|--------|-------------|-----------------|--------|--------------|--------|
| 1 | "if x > 0:" + Enter | - | - | - | - | Multi-line | `lines=["if x > 0:"]` | - |
| 2 | Tab | `""` | 0 | N/A | - | Insert 4 sp | `"    "` | 4 |
| 3 | "if y > 0:" + Enter | `"    if y > 0:"` | 13 | - | - | Multi-line | `lines=[...2 lines]` | - |
| 4 | Tab | `""` | 0 | N/A | - | Insert 4 sp | `"    "` | 4 |
| 5 | Tab | `"    "` | 4 | N/A | - | Insert 4 sp | `"        "` | 8 |
| 6 | **Backspace** | `"        "` | 8 | ✅ YES | ❌ NO (8→4) | Delete 4 sp | `"    "` | 4 |
| 7 | **Backspace** | `"    "` | 4 | ✅ YES | ⚠️ YES (4→0) | Delete 1 sp | `"   "` | 3 |

---

## Key Observations

### First Backspace (Step 6): Normal Smart Backspace
```
Buffer: "        " (8 spaces)
→ Deleting 4 leaves 4 spaces
→ Buffer NOT empty
→ Action: Delete 4 spaces ✓
```

### Second Backspace (Step 7): Empty Buffer Prevention
```
Buffer: "    " (4 spaces)
→ Deleting 4 leaves 0 spaces  ← Would be EMPTY!
→ Buffer would be completely empty
→ Action: Delete ONLY 1 space to prevent empty buffer ⚠️
```

---

## What You'd See On Screen

```
>>> if x > 0:
...     if y > 0:
...         ← After Tab + Tab (8 spaces)
...     ← After first Backspace (4 spaces)
...    ← After second Backspace (3 spaces, prevented empty!)
```

---

## The Logic

```rust
// First Backspace
buffer = "        " (8 spaces)
would_be_empty = !false && 8 == 4  // false
→ Delete 4 spaces normally

// Second Backspace
buffer = "    " (4 spaces)
would_be_empty = !false && 4 == 4  // true ← TRIGGERED!
→ Delete only 1 space (override)
```
