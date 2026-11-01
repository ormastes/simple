# rti007: declared returns that lower to `Any` get no RTI row in the frozen stage2 (2026-11-01)

Bug id: `rti007_any_return_rows_2026-11-01` (every `@workaround` tag of this family
references it). Successor of `rti007_mir_2026-10-31.md` (bare `-> Result` in the linker
modules, same root bug, different producers).

## Symptom

Phase-3 Windows bootstrap (frozen stage2 `C:/dev/p3new/stage2.exe`, source revision
ef0681fc0e1 = 2026-10-27, compiling current `release/1.0.0`; run 12 at 640144fa932,
log `C:/dev/p3new/r11/build.log.err`) fails MIR lowering of whole modules with

```
E-RTI-007: callee 'fn:X' of module 'M': E-RTI-007: declared return is Any; not representable in an interface row
E-RTI-007: callee 'enum:Poll::unwrap' of module 'lib.nogc_async_mut.async.poll': E-RTI-007: type parameter 'T' is not bound by the callable or its owner
```

The row is built at `src/compiler/20.hir/return_type_interface_v1.spl`
(`rti_row_from_signature_v1` -> `rti_term_of_hir_type`). The stage2 copy of that file
rejects `HirTypeKind.Any` outright; the error aborts registration of the provider module,
and every importer of a sibling callee then sees `E-RTI-002 ... has no exact return-type row`.

## Root cause (per producer; which HIR path yields `Any`)

| Pattern | Producer (stage2 ef0681fc0e1) | Fixed at HEAD by |
|---|---|---|
| generic `extern fn rt_*<T>(..) -> T?` / `-> T` (`rt_tuple_get`, `rt_mutex_lock`, `rt_mutex_try_lock`, `rt_enum_new`) | extern generics are not published with a semantic symbol type; the HIR signature lowers the unbound binder through the "bare single uppercase letter -> Any" seed-parity rule in `hir_lowering/types.spl` | 1c8132a5952 / b6d71af144b (semantic declared returns), 933a0979878 (Any = erased row) |
| explicit `Option<Result<..>>` (`InterpreterBackendImpl::try_call_builtin`) | phase-2 parser collapsed an explicit `Option<composite>` to the argless `TYPE_OPTION` tag -> `Optional(Any)` | f512a01c535 (preserve composite payload tags in explicit Option types) |
| untyped parameter + value return (`char_to_digit_safe(ch)`, `gzip_analyze_data(data)`) | `declaration_lowering.spl`: a function with an untyped parameter is dynamically typed, so its value return is `Any`; on the bootstrap route `infer_untyped_return_type` also returns `Any` when the body value is ambiguous | 933a0979878 (erased row) |
| unbound type name in a method return (`Map<K,V>::map_values(..) -> Map<K, U>`, no `<U>` binder) | `U` is not a binder of the callable or its owner -> `Any` argument | source bug; `<U>` added here |
| owner binder returned by a generic **enum** method (`Poll<T>::unwrap() -> T`) | stage2 `rti_owner_type_params` knew struct/class owners only | d2e2813c37d (retain enum owner type parameter binders) |
| bare `-> Result` (linker modules) | `Result<Any, Any>` payload | tracked in `rti007_mir_2026-10-31.md` |

RTI design decision (HEAD, `rti_builtin_of_kind`): a declared return that is genuinely
dynamic becomes the opaque builtin term `b:any`; the callee keeps exactly one row, callers
bind it back to `HirTypeKind.Any`. Concrete declared shapes must never reach that arm;
`test/01_unit/compiler/hir/return_type_interface_any_rows_spec.spl` pins one `it` per
producer pattern above (red on the ef0681fc0e1 producers, green at HEAD by construction of
the commits in the table).

Owner area: `src/compiler/20.hir` (return_type_interface_v1, hir_lowering/types,
_Items/declaration_lowering, _Items/module_callable_types) and the phase-2 parser type
registry (`src/compiler/10.frontend/core/parser.spl`).

## Minimal repro (frozen stage2)

```simple
# repro.spl -- any one of these declarations makes the module fail with E-RTI-007 in stage2
extern fn rt_probe_get<T>(tuple: i64, index: i64) -> T?        # generic extern
fn f_opt(name: text) -> Option<Result<text, text>>:            # explicit Option<composite>
    None
fn f_untyped(ch):                                              # untyped param, value return
    if ch == "0": return 0
    1
enum Poll<T>:
    Ready(T)
    Pending
impl Poll<T>:
    fn unwrap() -> T:                                          # enum owner binder
        match self:
            case Poll.Ready(v): v
            case Poll.Pending: panic("pending")
```

`C:/dev/p3new/stage2.exe native-build --entry-closure --entry <file> --source src/compiler
--source src/app --source src/lib --target x86_64-pc-windows-gnu --backend llvm` reports the
E-RTI-007 lines above during `phase=mir`.

## Workaround sites (all tagged `@workaround bug=rti007_any_return_rows_2026-11-01`)

Phase 3 runs on the frozen stage2, so the compiler fix cannot help it; the source must avoid
the `Any` producers. Every change keeps the runtime ABI (`src/runtime/runtime_native.c`:
`rt_tuple_get`, `rt_mutex_lock`, `rt_mutex_try_lock`, `rt_enum_new` all return a raw
`int64_t`, nil-sentinel on absence) and follows the existing non-generic precedent
(`src/compiler/10.frontend/parser_types_expr.spl:38`, `cranelift_codegen_adapter.spl:606`:
`extern fn rt_tuple_get(..) -> i64` read into typed locals).

- `src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl`: `rt_tuple_get` non-generic `-> i64`; three typed reads drop `<Expr>`/`<Block>`/`<Block?>`
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`: same; `_sffi_tuple_get<T>` wrapper unchanged
- `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`: same
- `src/lib/nogc_sync_mut/concurrent/mutex.spl`: `rt_mutex_lock`/`rt_mutex_try_lock` non-generic `-> i64`; the two `val current` nil-checked locals are typed `T?`; `lock<T>`/`try_lock<T>`/`mutex_lock_gate`/`mutex_try_lock<T>` keep their optional signatures
- `src/lib/nogc_sync_mut/sffi/enum_wire.spl`: `rt_enum_new` non-generic `-> i64`; `val restored: T = rt_enum_new(..)`
- `src/lib/nogc_sync_mut/src/map.spl`: `map_values<U>` (missing binder; this one is a real source fix, keep it)
- `src/lib/common/serialization/__init__.spl`: `char_to_digit_safe(ch: text) -> i64` (all returns are integer literals / `0`)
- Run 13 sweep (`deep_equal_list_text` was the next site; E-RTI-007 only reports the first failing callee per module, so the rest were found statically): every function in the stage3 import closure of `src/app/cli/bootstrap_main.spl` (~1400 files, alias-resolved `use` crawl) that has an untyped parameter and no declared return. All are in `src/lib/common/serialization/__init__.spl` (48 functions + 3 typed-param inferred returns: `escape_string`, `structural_hash_text`, `hex_to_bytes`) plus `src/lib/common/text_advanced.spl:number_lines`. Each now declares its return; parameters are typed where every caller is concrete (`bytes_to_hex`/`int_to_hex`/`serialize_list`-family/`pretty_print`/`define_schema` keep untyped params because callers pass `[u8]`, tuples or mixed lists). The same scan found no further generic `extern fn rt_*<T> -> T`, explicit `Option<composite>`, enum-owner-binder or unbound-type-name returns in the closure. Regression: `test/01_unit/lib/common/serialization_rti007_typed_returns_spec.spl`.
- `src/compiler/70.backend/backend/interpreter_calls.spl`: `try_call_builtin(..) -> Result<Value, BackendError>?` (postfix optional keeps the payload tag in stage2)
- `src/lib/nogc_async_mut/async/poll.spl`: `Poll::unwrap()` method removed; `poll_unwrap(p)` is the existing free equivalent (no `.unwrap()` call on a `Poll` value exists in the tree; `driver_hir_pipeline_lowering.spl:1628` even records `.unwrap()` being stolen by `Poll.unwrap` on the native lane)

## Removal condition

Remove the tagged sites once the stage2 used for bootstrapping contains 933a0979878,
f512a01c535, d2e2813c37d and 1c8132a5952 (i.e. after the next stage2 refresh from a
`release/1.0.0` revision at or after 8a935437a98). `map_values<U>` stays.

## Evidence

- Run 12 inventory (`C:/dev/p3new/r11/build.log.err`): 9 distinct callees, listed in the
  table above; after the sites were rewritten, a stage2 `native-build --entry-closure` of a
  416-module closure (frontend + HIR lowering + lib, entry importing
  `compiler.hir.hir_lowering.types`) no longer reports `E-RTI-007` for
  `module_callable_types` / `async.poll` (see the PR description for the exact run).
