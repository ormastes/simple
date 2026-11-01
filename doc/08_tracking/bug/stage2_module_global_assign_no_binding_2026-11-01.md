# Stage2 MIR: `None`-initialized optional module global has no static; assignment fails

- **ID:** stage2_module_global_assign_no_binding_2026-11-01
- **Priority:** P1 (blocks phase-3 stage3 MIR)
- **Status:** workaround in source (tagged); root fix open
- **Owner area:** `src/compiler/50.mir/_MirLowering/module_lowering.spl`
  (`runtime_module_initializer_supported` / `lower_static`)
- **Found by:** phase-3 run 14c, frozen stage2 `C:/dev/p3new/stage2.exe`
  (ef0681fc0e1), release/1.0.0 at 5fad50cca24

## Symptom

```
[go-to-end] failed stage=mir module=compiler.driver.driver_build.incremental:
MIR lowering error: assignment target has no local binding at
.../src/compiler/80.driver/driver_build/incremental.spl:1911:5
```

Line 1911 is `_incremental_macro_inventory_memo_v1 = Some(inventory)`. The
preceding `_incremental_macro_inventory_memo_key_v1 = key` (a `text = ""`
global) lowers fine.

## Cause

`runtime_module_initializer_supported` decides whether a module `var` gets a
`MirStatic`. It has arms for `NilLit`, `StringLit`, `Call`, `Binary`,
`MethodCall`, `ArrayLit`, `DictLit`, `TupleLit`, and a type fallback that
admits only `Int | Float | Bool | Str`. The initializer `None` matches none of
them, and an Optional type is not in the fallback, so it returns false.
`lower_static` then emits no static and records no `global_statics_by_id`
entry. `lower_assign_var` misses both `find_global_static` and `find_local` and
reports "assignment target has no local binding". This is the same defect class
as the earlier ArrayLit, DictLit and TupleLit gaps. The 54 tree sites spelled
`var G: T? = nil` compile because of the `NilLit` arm.

## Minimal repro (two files)

`memo/mod.spl`:

```simple
struct Inv:
    n: i64

var _memo_key: text = ""
var _memo: Inv? = None

pub fn memo_get(key: text) -> i64:
    if key == _memo_key:
        if val m = _memo:
            return m.n
    val inv = Inv(n: key.len())
    _memo_key = key
    _memo = Some(inv)
    inv.n
```

`main.spl`: `use memo.mod.{memo_get}` / `fn main(): print memo_get("abc")`

`stage2.exe compile main.spl --format=smf --source . --keep-going --go-to-end`
gives `MIR lowering error: assignment target has no local binding at
memo/mod.spl:13:5`. With `= nil`, MIR passes. It then stops at SMF packaging
("needs ELF object code, but the backend produced a COFF object"), which is an
unrelated Windows host limit.

## Workaround (tagged, behavior-identical)

`= None` becomes `= nil` on the three tree sites with this shape (Option
`<T>` was rewritten to `T?`, the same type):

- `src/compiler/80.driver/driver_build/incremental.spl` `_incremental_macro_inventory_memo_v1`
- `src/lib/nogc_sync_mut/replay/core/replay_engine.spl` `_g_engine`
- `src/lib/nogc_sync_mut/replay/semantic/trace_writer.spl` `GLOBAL_WRITER`

A full-tree grep of src/lib, src/compiler, src/app and src/plugins for
`^var X: ...? = None` and `^var X: Option<...> = None` finds no other sites.

## Root fix (open)

Add `case NilLit | <None variant>` handling (or an Optional arm in
`runtime_module_initializer_type_fallback`) so a `None` initializer gets a
runtime-initialized static, as ArrayLit and DictLit do. Revert the workaround
once a stage2 with the fix is frozen.

## Regression

`test/01_unit/compiler/50.mir/stage2_module_global_optional_assign_binding_spec.spl`
(not executed in this change).
