# Native: module-level `var x = false` is garbage-truthy at startup

**Severity:** P1
**Date:** 2026-06-13
**Area:** native codegen (module-level var initialization)
**Related:** baremetal module-level `val` zeroing (`feedback_baremetal_module_val_zero`), native env_get raw pointer (`native_env_get_raw_pointer_2026-06-12.md`)

**Status (2026-07-15):** Pure-Simple scalar-global initialization fix landed.
Strict default-LLVM + explicit-Cranelift direct/getter first-read regression added to
`scripts/check/check-native-seed-parity.shs`; execution awaits a fresh
pure-Simple compiler binary.

## Repro

```simple
var FLAG = false
var COUNT = 0

fn check_flag() -> bool:
    FLAG

fn main():
    if check_flag():
        print "FLAG truthy (BUG)"
    else:
        print "FLAG false (ok)"
    if FLAG:
        print "direct truthy (BUG)"
    else:
        print "direct false (ok)"
    print "count={COUNT}"
```

`bin/simple native-build --runtime-bundle core-c-bootstrap --entry m.spl --output m && ./m`:

```
FLAG truthy (BUG)
direct truthy (BUG)
count=0
```

Interpreter (`bin/simple run m.spl`) prints both `false (ok)` paths.

- `var COUNT = 0` (i64) initializes correctly natively.
- `var FLAG = false` (bool) reads truthy both directly and via a getter fn.

## Impact

Any native binary using module-level bool flags silently misbehaves. Found
because the MCP server's auto-mode dynload state machine
(`_MCP_LIST_UPGRADED`/`_MCP_EMIT_LIST_CHANGED = false`) served the full list
on first tools/list and emitted spurious `list_changed` notifications in
all/core modes — while all 14 interpreter spec tests passed. Wire-level
native verification caught it.

## Workaround

Use i64 0/1 module-level flags; keep bool-returning accessor fns
(`flag == 1`). Applied in `src/app/mcp/main.spl`.

## Second finding (same session): read+write same fn → read sees nil (BOTH modes)

A fn that both READS and ASSIGNS the same module-level var sees `nil` on the
read — in interpreter AND native. A read-only getter fn in between fixes it:

```simple
var F = 0
fn arm():            # write-only: works, module F becomes 1
    F = 1
fn take() -> bool:   # read+write: F read is nil -> false  (BUG, both modes)
    val v = F == 1
    F = 0
    v
fn take_g() -> bool: # getter-mediated read: works
    val v = getf() == 1
    F = 0
    v
```

Looks like assignment anywhere in the body makes the name resolve to an
uninitialized local for reads (Python-style local hoisting without `global`).
Also observed: string interpolation `"{F}"` of a module-level var prints
`nil` even in fns that never assign it.

Workaround applied in `src/app/mcp/main.spl`: `_mcp_upgraded_value()` /
`_mcp_emit_flag_value()` read-only getters.

## Fix direction (hypothesis — verify against codegen)

Module-level bool initializers likely skip the global-init path that i64
literals take (uninitialized BSS/data slot read as nonzero, or boxed-value
slot read before init). Check where global `var` initializers are lowered in
native entry-closure builds; bool literal may be dropped or mis-sized.
