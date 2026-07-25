# Native: module-level `var x = false` is garbage-truthy at startup

**Severity:** P1
**Date:** 2026-06-13
**Area:** native codegen (module-level var initialization)
**Related:** baremetal module-level `val` zeroing (`feedback_baremetal_module_val_zero`), native env_get raw pointer (`native_env_get_raw_pointer_2026-06-12.md`)

**Status (2026-07-16): RESOLVED (scalar bool/i64 module globals).** Pure-Simple
scalar-global initialization fix landed 2026-07-15 and is now native-verified.
Strict default-LLVM + explicit-Cranelift direct/getter first-read regression added to
`scripts/check/check-native-seed-parity.shs`
(`write_case_module_global_false_first_read`). The same regression covers
read-then-write name resolution and interpolation of the module slot.

`var s = ""` (text) module globals are NOT covered by this fix — that is a
distinct codegen bug, filed separately (see Regression evidence below).

## Regression evidence (2026-07-16, lane modvar_bool)

Native-build verification of the scalar cases (bool + i64):

```
# var FLAG = false / var COUNT = 0, read at startup then mutated
$ env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry pb.spl -o pb --clean && ./pb
FLAG false (ok)
direct false (ok)
count=0
after true (ok)
count2=7            # rc=0
```

`var FLAG = false` reads false directly and via a getter fn; `var COUNT = 0`
reads 0; both mutate and re-read correctly. The existing parity probe
`write_case_module_global_false_first_read` (bool first-read + read-then-write
+ `{state}` interpolation) builds and prints `00|73|state=3` natively (rc=0),
its expected value — the fix is confirmed.

Verification caveats (see Fix direction / CONFLICT notes):
- The seed interpreter `bin/simple run` (stale compiled-in interpreter) still
  prints the OLD buggy `FLAG truthy (BUG)` for this repro, so it is not a valid
  oracle here; the live-`src/compiler` native path is the correct reference and
  emits the fixed `false` values.
- At the target commit the seed cannot load current `src/compiler`
  (`error: semantic: type mismatch: cannot convert dict to int`), so
  `native-smoke-matrix.shs` and the parity harness cannot execute there
  (`total=15 pass=0 fail=15` — all "build-failed", a seed↔source regression
  independent of this bug). The scalar verification above was run at commit
  `5c67273d180`, where `bootstrap_globals.spl` is byte-identical to the target
  and native-build loads cleanly.

## Third finding (2026-07-16): `var s = ""` text global → llc type mismatch

Filed as `doc/08_tracking/bug/native_module_var_text_global_type_mismatch_2026-07-16.md`.
Module-level `var NAME = ""` emits `@g_NAME = global i64 <ptr getelementptr>`,
which `llc` rejects (`constant expression type mismatch: got type 'ptr' but
expected 'i64'`) — the global slot type (`i64`) and the string initializer
(`ptr`) disagree in `core_codegen.spl` around the
`{g_name} = global {g_ty} {g_init}` emit. Distinct from the bool/i64 scalar
fix; text globals need a runtime-handle init, not a raw char* constant.

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

**Resolved in source (2026-07-15):** MIR global reads and writes now route the
resolved module binding through the shared symbol id. The strict dual-backend
case now proves a read followed by a write in one function and a subsequent
interpolated read of the same module slot. Runtime execution remains pending the
fresh pure-Simple compiler binary noted above.

The original failure was that a fn which both READS and ASSIGNS the same
module-level var saw `nil` on the read — in interpreter AND native. A read-only
getter fn in between fixed it:

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
