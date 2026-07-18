# Bug: Native List Indexing with Loop Variables

Status: resolved (2026-06-14)

**Date:** 2026-06-05
**Severity:** High
**Component:** compiler/codegen (Cranelift native)
**Status:** resolved (2026-06-14)

## Resolution (2026-06-14)

Root cause: in `for i in 0..N`, HIR `Node::For` lowering
(`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`) gave the loop var
`TypeId::ANY` because the `rt_range` builtin iterable reports element type `ANY`.
An untagged i64 loop var then skipped `rt_value_to_string` boxing → formatted as
`<value:0x1>` and corrupted list indexing. Fix: infer the concrete integer
element type from the `rt_range`/`rt_range_inclusive` start argument (default
`TypeId::I64`). Verified: native build of the loop-index repro now matches the
interpreter exactly. Requires seed rebuild to deploy. (Same i64-boxing family as
the `native-build` codegen notes in
`lsp_mcp_integer_position_args_corrupted_2026-06-14`.)

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
