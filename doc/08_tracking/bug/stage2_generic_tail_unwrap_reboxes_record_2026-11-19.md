# Erased generic `-> T` tail `.unwrap()` int-boxes a record payload (Stage 3 MIR SIGSEGV)

- **Date:** 2026-11-19
- **Status:** workaround in source (`# @workaround bug=stage2_generic_tail_unwrap_reboxes_record_2026-11-19`);
  lowering fix open (needs a new Stage 2 to prove, see "Not done")
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

## Not done

- The lowering fix. The `.unwrap()` arm should treat an erased `TypeParam` payload as
  the `T` slot's tagged word, so that the `-> T` boundary does not re-box it. The same
  applies to a `match` tail. Proving this needs a new Stage 2, which is out of scope for
  this lane. The integer case currently round-trips only because the payload is raw, so
  a naive "mark the result as a runtime value" change could break `T=i64` callers. Read
  how the `if val` binder lowers before changing it.
- Whether the Stage 3 self-build gets past MIR with this workaround still needs a fresh
  Stage 3 build to confirm.
