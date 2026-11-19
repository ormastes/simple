# Erased generic `-> T` tail `.unwrap()` int-boxes a record payload (Stage 3 MIR SIGSEGV)

- **Date:** 2026-11-19
- **Status:** workaround in source (`# @workaround bug=stage2_generic_tail_unwrap_reboxes_record_2026-11-19`);
  the fixture's `tuple_at` forwarder shape cannot be fixed soundly in 50.mir, so
  the workaround IS the fix for it (see "Lowering fix"); a sibling double-box for
  argument-bound producers is fixed in MIR (native proof needs a Stage 2 built from it)
- **Lane:** Stage 2 (integ18, cranelift) -> Stage 3 -> Stage 3 self-build, aarch64 Linux
- **Source pin:** release/1.0.0 `cbff0ece9e8`
- **Family:** `stage3_array_copy_unique_static_leaf_2026-11-19.md`,
  `optional_record_array_store_keeps_option_box_2026-11-19.md`

## Symptom

The Stage 3 self-build passes parse, surface and HIR of all 1599 modules. Then the first
MIR shard worker dies:

```
[mir-shard] owner=0/14@0 status=CRASH exit=-139 ... signal=SIGSEGV(11)
ICE[mir_lower] module compiler.mir._MirLoweringExpr.switch_operators_calls (attributed)
```

Worker 1 died the same way on `expr_dispatch`. Neither module is the cause: any index
read crashes Stage 3 MIR lowering. A 3-line `val a = [1, 2]; val x = a[1]` program is
enough. Stage 3's LLVM codegen also SIGSEGVs, even on hello world (same helper in
`core_codegen.spl`).

## Backtrace (Stage 3, gdb)

```
#0 MirLowering.lower_index_expr            +0xdc  ldr x5,[x5]   x5 = 0x55555a794bf08
#1 MirLowering.lower_index_expr_from_hir
#2 lower_expr_impl <- lower_expr <- lower_expr_for_slot <- lower_stmt_impl <- lower_block
   <- lower_function <- lower_module ...
```

The fault is in `lower_index_expr`'s prologue, where it copies the `base: HirExpr`
argument. The caller passed a non-pointer word.

## Root cause

`lower_index_expr_from_hir` reads the Index children through
`_sffi_tuple_get_req<HirExpr>(payload, 0)`.

```
fn _sffi_tuple_get_req<T>(tuple: i64, index: i64) -> T:
    compiler_value_tuple_at<T>(tuple, index).unwrap()
```

Generics have one erased body. Stage 2 lowered this body as follows. The disassembly of
`expr_dispatch._sffi_tuple_get_req` in the Stage 3 binary shows it:

1. `compiler_value_tuple_at`, then `rt_is_some` / `rt_panic` / `rt_unwrap_or_self`
   (`.unwrap()`, `method_calls_literals.spl` Option arm). The inner type is `TypeParam`,
   so `lower_type` gives `I64`, `enum_payload_value` passes the word through unchanged,
   and the result is not marked as a runtime value.
2. The `-> T` tail (`function_lowering.spl`, `case Any | TypeParam`) calls
   `box_runtime_value`. That sees an unmarked `I64` local and emits
   `rt_value_int_wide(word)`, boxing the record handle as an integer.

An integer `T` round-trips correctly. A record, text or array `T` comes back as a
shifted garbage word. The `if val present = ...: return present` form is lowered
correctly for all four kinds.

## Fixture (`test/fixtures/native_generic_tail_unwrap_record/main.spl`)

The fixture has the same shape as the compiler helper: an enum payload tuple, a generic
`get_req<T>` with a tail `.unwrap()`, and `T` = a record. Results with `check_fx.sh`
(seed interpreter vs integ18 Stage 2):

| variant | cranelift | llvm |
|---|---|---|
| tail `tuple_at<T>(..).unwrap()` (fixture) | run=139, no output | run=139 |
| `if val present = ..: return present` + `panic` | SAME | SAME |
| same, `rt_tuple_get` inside `unsafe` (backend shape) | SAME | SAME |
| `fn req<T>(v: T?) -> T: v.unwrap()`, T=i64 | SAME | SAME |
| same, T=text / T=record | run=139 | run=139 |
| same body as `match v: case Some(x): x` | run=139 | run=139 |

Seed output: `1 left 2 right`.

## Workaround

Both `_sffi_tuple_get_req` copies now use the `if val` + explicit `return` + `panic` form:
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` and
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`. These are the only two
generic `-> T` functions in `src/compiler`, `src/app` and `src/lib` whose tail is
`.unwrap()`. The new form adds no call on the hot path: one presence test, as before.

## Lowering fix (2026-11-19)

**The fixture's shape is ambiguous inside the erased body.** `rt_tuple_get` returns
the stored tuple word verbatim, and an enum payload tuple stores RAW scalars
(`NI.Two(7, 9)` lowers to `rt_tuple_set(t, 0, 7)`, no `Shl`/`rt_value_int_wide`).
So in `get_req<T>` the unwrapped word is a raw 7 for `T=i64` and a handle for
`T=Pair`; the tail box is right for the first and wrong for the second, and the
erased body cannot tell them apart. Marking that word as a runtime value would
make `get_req<i64>` return 7 and its caller decode `7 >> 3 = 0`. Every in-tree
instantiation of `_sffi_tuple_get_req` is a record or enum (`HirExpr` x7,
`LocalId` x4, `AggregateKind`, `MirConstValue`, `MirType`), so for that shape the
`if val` + `return` workaround is the fix, not a stopgap.

**What is fixed (MIR):** `option_unwrap_payload_is_erased_tagged_v1`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`) marks the
`.unwrap()` result as a runtime value only for a direct call to a free function
whose `T?` result's `T` is also carried by an ENCODED parameter slot (bare `T`,
`[T]`, `Dict<K, T>`), e.g. `head<T>(xs) -> T: first(xs).unwrap()`. That is the
same proof `decode_erased_scalar_call_payload` uses at a concrete caller (the slot
test is now the shared `erased_encoded_slot_param_v1`). Such a callee stores the
tagged `T` word, and the old tail re-boxed it: `T=i64` came back tagged twice
(caller boxes 5 -> 40, tail -> 320, caller decodes 40) and a record handle shifted.
`T?` parameters, closure results, generic-class methods (plain `T`) and forwarders
without an encoded slot keep the
tail box.

Spec: `test/01_unit/compiler/mir/generic_tail_unwrap_record_spec.spl` (1 of 9 red
before, 9/9 after). Per-function MIR of the 18-function probe module before and
after is byte-identical except `head`.

## Not done

- The durable fix for the `tuple_at` forwarder shape is a producer/extern contract,
  not MIR: restrict `_sffi_tuple_get_req` / `compiler_value_tuple_at` to handle-typed
  `T`, or decode in a typed concrete wrapper.
- The `T?` PARAMETER shape (`fn req<T>(v: T?) -> T: v.unwrap()`, T = record) still
  re-boxes: a concrete caller passes `rt_enum_new(1, 0, raw)`. The fix belongs on the
  caller side (box the payload of a `T?` argument). The `match v: case Some(x): x`
  tail is not changed. `if val p = v: return p` on a param never boxes, so it returns
  a raw int that the caller then decodes; check that case before relying on it.
- `fn get_or<T>(f: fn() -> T?) -> T: f().unwrap()` called with a concrete
  `\() -> i64?: Some(5)` lambda: the caller (`use_get_or` in the probe) has no decode
  at all. Pre-existing, not investigated here.
- Whether the Stage 3 self-build gets past MIR with this workaround still needs a fresh
  Stage 3 build to confirm.
