# Constructor Pattern Fix & Clarification

**Date:** 2026-01-23
**Status:** FIXED - Interpreter now supports methods in class bodies with dict/list assignment

---

## What Was Fixed

**Interpreter Bug:** Dict and list assignment through field access in mutable methods now works.

```simple
class Cache:
    items: Dict<text, i32>

    me store(key: text, value: i32):
        self.items[key] = value  # ✅ NOW WORKS (was failing before)

fn test():
    val cache = Cache(items: {})
    cache.store("key", 123)      # ✅ Works!
```

**File Changed:** `src/rust/compiler/src/interpreter/node_exec.rs`
- Added support for index assignment on field accesses: `self.field[key] = value`
- Now handles both: `container[i] = value` and `self.container[i] = value`

---

## Constructor Pattern Clarification

### ❌ WRONG - Don't do this:

```simple
class StringInterner:
    strings: Dict<text, i32>

    static fn new() -> StringInterner:  # ❌ Not needed!
        StringInterner(strings: {})

fn test():
    val s = StringInterner.new()  # ❌ Wrong - don't use .new()
```

### ✅ CORRECT - Do this instead:

```simple
class StringInterner:
    strings: Dict<text, i32>

fn test():
    val s = StringInterner(strings: {})  # ✅ Direct construction
```

### Pattern Summary

| Pattern | Description | Usage |
|---------|-------------|-------|
| `ClassName(field: value)` | Direct construction (PRIMARY) | `Point(x: 3, y: 4)` |
| `ClassName.factory()` | Named factory method (optional) | `Point.origin()` |
| `ClassName.new()` | ❌ DON'T USE - not idiomatic | Avoid |

---

## Method Patterns in Class Bodies

Both patterns work now (thanks to the interpreter fix):

### Pattern 1: Methods in Class Body

```simple
class Point:
    x: i64
    y: i64

    fn distance() -> f64:           # ✅ Immutable method in class
        (self.x * self.x + self.y * self.y).sqrt()

    me move(dx: i64, dy: i64):      # ✅ Mutable method in class
        self.x = self.x + dx
        self.y = self.y + dy
```

### Pattern 2: Methods in Impl Block

```simple
class Point:
    x: i64
    y: i64

impl Point:
    fn distance() -> f64:           # ✅ Immutable method in impl
        (self.x * self.x + self.y * self.y).sqrt()

    me move(dx: i64, dy: i64):      # ✅ Mutable method in impl
        self.x = self.x + dx
        self.y = self.y + dy
```

**Both work!** Choose whichever is clearer for your code.

---

## Key Points About Constructors

1. **No special constructor method needed** - just call `ClassName(field: value)`
2. **Constructor call creates AND initializes instance** - unlike Python's `__init__`
3. **Static factory methods are optional** - only use them when needed
4. **Keep constructor simple** - complex initialization goes in `impl` block

---

## Documentation Updated

**CLAUDE.md** now clearly states:

- ✅ Define constructors by defining the class
- ✅ Call constructors with `ClassName(field: value)`
- ✅ Use static factory methods ONLY when they add value
- ❌ Don't create `.new()` methods - they're unnecessary

---

## What This Enables

With the interpreter fix, these patterns now work:

```simple
class StringInterner:
    strings: Dict<text, i32>
    reverse: Dict<i32, text>
    next_id: i32

    me intern(s: text) -> i32:
        if self.strings.contains_key(s):
            return self.strings[s]

        val id = self.next_id
        self.strings[s] = id              # ✅ Fixed!
        self.reverse[id] = s              # ✅ Fixed!
        self.next_id = self.next_id + 1
        id

class Cache:
    data: Dict<text, List<i32>>

    me add_item(key: text, value: i32):
        if not self.data.contains_key(key):
            self.data[key] = []           # ✅ Create new list
        self.data[key].push(value)        # ✅ Add to list
```

---

## Summary

**Before Fix:**
- ❌ Methods in class bodies with dict/list assignment: `self.dict[key] = value` failed
- ❌ Tree-sitter tests blocked by "invalid assignment" error

**After Fix:**
- ✅ Methods in class bodies with dict/list assignment: works!
- ✅ Can use mutable methods to build up complex data structures
- ✅ Code is more Pythonic and less verbose than Rust-style

**Pattern Clarification:**
- ✅ CLAUDE.md now clearly documents constructor patterns
- ✅ Emphasizes direct construction, not `.new()`
- ✅ Shows both in-class and impl-block method patterns

**Result:**
All tree-sitter implementation files with mutable methods now work correctly!
