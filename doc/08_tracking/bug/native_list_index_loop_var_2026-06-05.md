# Bug: Native List Indexing with Loop Variables

Status: Open

**Date:** 2026-06-05
**Severity:** High
**Component:** compiler/codegen (Cranelift native)
**Status:** Open

## Description

In native compiled mode, `list[i]` where `i` is a `for` loop variable produces
incorrect index values after the first iteration. Also, `for h in list` iteration
over `List<StructType>` segfaults, and `list.length()` fails with
"function not found: Array.length".

## Reproduction

```simple
fn main():
    var items: List<i64> = []
    items.push(10)
    items.push(20)
    items.push(30)
    items.push(40)
    for i in 0..4:
        println("items[{i}] = {items[i]}")
```

**Expected:**
```
items[0] = 10
items[1] = 20
items[2] = 30
items[3] = 40
```

**Actual (native):**
```
len =
items[0] = 10
items[<value:0x1>] = 20
items[0] = 30
items[] = 40
```

## Impact

Any native-compiled code using List with index-based access in a loop produces
wrong results. Workaround: use explicit variables instead of List collection.

## Related

- `for h in list` iteration over `List<StructType>` segfaults in native mode.
- `list.pop()` also segfaults in native mode.
- Interpreter mode handles all of these correctly.
