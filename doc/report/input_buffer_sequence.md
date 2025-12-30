# Input and Buffer Sequence - Complete Log

**What the user typed and what happened to the buffer**

---

## Sequence 1: Tab → Backspace

### Event 1: User presses Tab
```
INPUT: Tab key
```

**Buffer BEFORE:**
```
buffer = ''        (empty)
cursor = 0
len    = 0
cap    = 0
```

**Buffer AFTER:**
```
buffer = '    '    (4 spaces inserted)
cursor = 4         (at end)
len    = 4
cap    = 8         (allocated)
```

---

### Event 2: User presses Backspace
```
INPUT: Backspace key
```

**Buffer BEFORE:**
```
buffer = '    '           (4 spaces)
cursor = 4                (at end)
len    = 4
cap    = 8
before_cursor = '    '    (all 4 spaces before cursor)
```

**Whitespace Check:**
```
before_cursor.chars().all(|c| c == ' ') → TRUE
→ In leading whitespace
→ Would delete 4 spaces normally
→ BUT: would_be_empty=true (4 spaces = whole buffer)
→ OVERRIDE: Delete only 1 space
```

**Buffer AFTER:**
```
buffer = '   '            (3 spaces remaining)
cursor = 3                (moved back 1)
len    = 3
cap    = 8                (no realloc)
```

---

## Sequence 2: Tab + Type "hello" + Backspace

### Event 3: User presses Tab (again)
```
INPUT: Tab key
```

**Buffer changes:** `'   '` → `'       '` (3 + 4 = 7 spaces)

---

### Event 4: User types 'h'
```
INPUT: 'h' key
```

**Buffer BEFORE:**
```
buffer = '       '        (7 spaces)
cursor = 7
len    = 7
cap    = 8
```

**Buffer AFTER:**
```
buffer = '       h'       (7 spaces + 'h')
cursor = 8
len    = 8
cap    = 8                (no realloc)
```

---

### Event 5: User types 'e'
```
INPUT: 'e' key
```

**Buffer BEFORE:**
```
buffer = '       h'
cursor = 8
len    = 8
cap    = 8
```

**Buffer AFTER:**
```
buffer = '       he'      (7 spaces + 'he')
cursor = 9
len    = 9
cap    = 16               (REALLOCATED 8→16)
```

---

### Event 6: User types 'l'
```
INPUT: 'l' key
```

**Buffer:** `'       he'` → `'       hel'`

---

### Event 7: User types 'l'
```
INPUT: 'l' key
```

**Buffer:** `'       hel'` → `'       hell'`

---

### Event 8: User types 'o'
```
INPUT: 'o' key
```

**Buffer BEFORE:**
```
buffer = '       hell'
cursor = 11
len    = 11
cap    = 16
```

**Buffer AFTER:**
```
buffer = '       hello'   (7 spaces + 'hello')
cursor = 12
len    = 12
cap    = 16
```

---

### Event 9: User presses Backspace
```
INPUT: Backspace key
```

**Buffer BEFORE:**
```
buffer = '       hello'          (7 spaces + 'hello')
cursor = 12                      (at end)
len    = 12
cap    = 16
before_cursor = '       hello'   (has text, not all spaces)
```

**Whitespace Check:**
```
before_cursor.chars().all(|c| c == ' ') → FALSE (has 'hello')
→ NOT in leading whitespace
→ Delete 1 character only
```

**Buffer AFTER:**
```
buffer = '       hell'           (deleted 'o')
cursor = 11                      (moved back 1)
len    = 11
cap    = 16                      (no realloc)
```

---

## Summary Table

| # | Input | Buffer Before | Cursor | Buffer After | Cursor | Check Result |
|---|-------|---------------|--------|--------------|--------|--------------|
| 1 | Tab | `''` | 0 | `'    '` (4 sp) | 4 | Insert 4 spaces |
| 2 | Backspace | `'    '` | 4 | `'   '` (3 sp) | 3 | Would be empty → delete 1 |
| 3 | Tab | `'   '` | 3 | `'       '` (7 sp) | 7 | Insert 4 spaces |
| 4 | 'h' | `'       '` | 7 | `'       h'` | 8 | Insert char |
| 5 | 'e' | `'       h'` | 8 | `'       he'` | 9 | Insert char (realloc) |
| 6 | 'l' | `'       he'` | 9 | `'       hel'` | 10 | Insert char |
| 7 | 'l' | `'       hel'` | 10 | `'       hell'` | 11 | Insert char |
| 8 | 'o' | `'       hell'` | 11 | `'       hello'` | 12 | Insert char |
| 9 | Backspace | `'       hello'` | 12 | `'       hell'` | 11 | Not whitespace → delete 1 |

---

## Key Points

### What is "before_cursor"?
```
before_cursor = buffer[0..cursor]  // Slice from start to cursor position
```

**Examples:**
- Buffer = `'    '`, cursor = 4 → `before_cursor = '    '` (all spaces)
- Buffer = `'       hello'`, cursor = 12 → `before_cursor = '       hello'` (has text)

### Whitespace Check Logic
```rust
if before_cursor.chars().all(|c| c == ' ') {
    // ALL characters from start to cursor are spaces
    // → "leading whitespace" (smart backspace)
} else {
    // Has non-space characters
    // → NOT leading whitespace (normal backspace)
}
```

### Empty Buffer Prevention
```rust
if would_be_empty {
    spaces_to_delete = 1  // Only delete 1 instead of 4
}
```

**When triggered:**
- Buffer only contains spaces
- Cursor at end (no content after)
- Deleting would make buffer completely empty
- Override: Delete only 1 space to keep buffer non-empty
