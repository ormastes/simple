# Native: erased generic class `T?` returns/params miscompile (2026-11-15)

**Status:** fixed / `@workaround` retired (2026-11-26). `AttributeStoreV1<T>` now stores `T?` uniformly across `owner: AttrOwnerV1<T>?`, `slots: [T?]`, and `hash: Dict<i64, T?>` (`Some(value)` / `case Some(v): return Ok(v)`), eliminating the mixed raw-vs-tagged ABI split inside `AttributeStoreV1<T>`. `nodes.spl` (`extra`, `op`) now uses `AttributeStoreV1<i64>` (`attr_store_detached_v1<i64>`), and `# @workaround bug=native_erased_generic_optional_return_2026-11-15` is retired from `attribute_schema_v1.spl` and `attribute_layouts_spec.spl`. Pre-fix Stage 2 (`81625788a20`) and `P3` (`162c481782f`, pre-`08ce3f6bb79`/pre-`#11865`) notes retained below for history.
`G<T>` repros below were run on an older Stage 2 (run 33,
`/home/yoon/dev/simple-boot-fable-20261112/build/bootstrap/pinned-src/pinned-8220cfef5b8a/build/bootstrap-fable-33/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`)
and on the Stage 2 built from `81625788a20` (pre-rebase sha of `1570c5778b8`). The true pre-fix base is run 34
(`.../pinned-43d59a399477/build/bootstrap-fable-34/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`).
The reviewer reproduced the trait-free SparseHash ÷8 below on it.

## Repro (`native-build main.spl --entry-closure`, SIMPLE_BOOTSTRAP=1)

```
class Box<T>:
    v: T?
impl Box<T>:
    fn read() -> T?:
        self.v
    fn none_read() -> T?:
        None
    me put(value: T):
        self.v = Some(value)

fn show_i64(tag: text, v: i64?):
    match v:
        case Some(x): print "{tag} some {x}"
        case None: print "{tag} none"

fn main():
    var b: Box<i64> = Box(v: Some(41))
    show_i64("i read", b.read())        # expect: i read some 41
    show_i64("i none", b.none_read())   # expect: i none none
    var f: Box<f64> = Box(v: Some(1.5))
    f.put(2.5)                          # cranelift: verifier error here
main()
```

- **llvm:** `i read some 196953466405569`, and `i none some <handle>`. The
  concrete caller re-wraps the generic method's Option handle as
  `Some(handle)`, because bootstrap HIR erases the template's `-> T?` return to
  i64 and generic-impl methods publish no Function symbol type. f64 prints
  denormals, which is the same double wrap.
- **cranelift:** `arg 1 (v200) has type f64, expected i64`. A raw f64 is
  passed into the erased `T` parameter.

## Why a signature-only fix is wrong

Publishing the `-> T?` signature for generic-impl methods removes the re-wrap
and the f64 arg error. However, `Some(value: T)` built inside an erased body
then carries a *tagged* runtime word (`rt_value_int_wide` = `v<<3|tag`, f64
heap-boxed), while concrete `X?` readers decode the payload *raw*
(`enum_payload_value`). That turns a refusal into silent wrong values, so it
was reverted. A real fix must pick one payload representation at the erased ↔
concrete boundary: either convert at call/return, or monomorphize.

## Same family: bool payload in a generic method's `Result`

```
class G<T>:
    n: i64
impl G<T>:
    me set(value: T) -> Result<bool, text>:
        Ok(true)
var g: G<i64> = G(n: 0)
match g.set(5):
    case Ok(b): print "set {b}"     # expect "set true"; native prints "set 1"
```

Pre-fix Stage 2, cranelift: `set 1`.

## Observed on the real module (Stage 2 `81625788a20` = rebased `1570c5778b8`, cranelift)

The real module returns WRONG i64 values natively; this is not limited to the
`set` bool. Results by shape (reviewer probes in
`build/review-trait/{real,real2,asnt,col_nt}`):

- **SparseHash, ÷8 (`Dict<i64, T>` payload).** In the `nodes.spl` shape,
  `9000000000 -> 1125000000` and `7 -> 0`. A trait-free copy of the store
  shows the same ÷8 on the pre-fix (run 34) and post-fix Stage 2, which is the
  3-bit runtime-tag shift.
- **Embedded and Column, ×8 in a helper-parameter shape.** When the store
  values pass through a helper's `Result<i64, text>` parameter,
  `9000000000 -> 72000000000` and `-5 -> -40`.
- **Correct:** Column in the `nodes.spl` shape, and every `text` store
  (direct, column, sparse_hash).
- My own narrower probe (direct/column, values read in place) printed correct
  i64 values except `set` printing `1` for `Ok(true)`. That shape simply
  missed the ÷8 and ×8 paths.

Until this is fixed, `src/compiler/10.frontend/core/_AstExpr/nodes.spl`
gates the non-direct `SIMPLE_NODE_ATTR` / `SIMPLE_NODE_ATTR_SDN` placements
behind a fresh-store round-trip self-check. On a mismatch it prints
`node-attr: <placement> store failed its round-trip self-check on this build;
staying on direct storage (...)` and keeps mode 0.

- **llvm:** the build fails in codegen for `sha256`, `sdn.parser`,
  `data_schema_resolver` and `data_schema_core_v1` (llc error: `'%lN' defined
  with type 'i64' but expected 'ptr'`). The same llc failure in `sha256` and
  `sdn.parser` reproduces on the pre-fix Stage 2 with a trivial importer.

## Store-side workaround (2026-11-17) — verification-pending

The codegen defect above stays **open**. The node-attr i64 attributes no longer
go through the erased store:

- `AttrI64StoreV1` (`src/compiler/00.common/data/attribute_schema_v1.spl`) is a
  concrete, non-generic i64 store for column / array_index / sparse_hash. No
  type parameter, no `[T?]` / `Dict<i64,T>` payload, no trait-object `T?`
  return (array_index keeps its node→slot table in a plain `[i64]`, -1 = none).
  Hash reads use `contains_key` + index per `dict_native_pitfalls.md`.
- `nodes.spl` builds the `extra` and `op` stores with `attr_i64_store_v1`, and
  `expr_attr_i64_round_trips` checks that same store (now also a `-5` value for
  the ×8 shape). The gate stays fail-closed. `s_val` stays on the generic
  `AttributeStoreV1<text>` (text was measured correct). Default stays OFF.
- Interpreter regression: `test/01_unit/compiler/data/attribute_layouts_spec.spl`
  ("concrete i64 node attribute store"), RED before the class existed, 11/11 GREEN after.

## Root cause pinned in MIR/LLVM (2026-11-17)

The SparseHash ÷8 is a write/read ABI split *inside one erased method
pair*, shown by the in-process HIR -> MIR -> LLVM spec
`test/01_unit/compiler/50.mir/generic_method_erased_i64_boundary_spec.spl`
(`GMEB_DUMP=1` prints the IR; run with `bin/simple.exe` of 11-17, the
11-13 `seed_p1.exe` can no longer parse `driver_compile_options.spl:63`):

```
Store.set:  %l7 = call @rt_value_int_wide(%key)       ; key encoded
            call @rt_dict_set(%h, %l7, %value)         ; VALUE stored RAW
Store.get:  %l19 = call @rt_dict_get(%h, %key_enc)
            %l20 = call @rt_value_as_int_wide(%l19)    ; read DECODES (>>3)
probe:      call @Store.set(ptr %s, i64 1, i64 %v)     ; caller passes v raw
```

Why: a generic-class method has an untyped symbol in bootstrap mode, so
its `T` arguments arrive plain ("plain in/out"), and `box_runtime_value`
leaves the `T` param unboxed at `rt_dict_set` (`mir_lowering_stmts.spl`
~2851). Concrete code and free generic fns write `Dict<K,T>` values
encoded, so the method READ must decode (b08: `Bag.lookup` over a
concretely built dict) — the method WRITE is the odd one out.

Why no body-side fix: inside the one erased body the runtime kind of a
plain `T` word is unknown (i64 raw vs f64 bits vs bool 0/1 vs a text/record
handle), so the body cannot pick `rt_value_int_wide` vs heap-box vs pass
through. Only the call site, where the receiver binds `T`, can encode.

Remaining scope (one change, not separable without a new silent ÷8/×8):
1. Encode method args into bare `T` / `[T]` / `Dict<K,T>` params at the call
   when the receiver instance binds `T` to a scalar (`box_runtime_value`, as
   `lower_call` already does for free fns).
2. Decode `T?` / `Result<T,E>` / bare `T` method results at the caller,
   binding `T` from the receiver's HIR type args
   (`decode_erased_scalar_call_payload` currently states methods never
   reach it); drop the body re-box of a bare `-> T` tail and the
   `current_fn_is_method` exemption in `lower_dict_runtime_read`.
3. Generic-class FIELDS of scalar `T` must then also be encoded at
   construct sites and decoded at concrete field reads — today
   `Box<i64>(v: Some(41))` stores raw (`infer_erased_call_result_instance`),
   so 1+2 alone would turn `Box.read()` into a ÷8.
The spec is tagged `@tag:in-development` and its third example is the
acceptance row for 1-3. The `AttrI64StoreV1` workaround stays.

Native verification needed: a Stage 2 rebuilt from this source run with
`SIMPLE_NODE_ATTR=extra=sparse_hash,op=sparse_hash` must not print the
`failed its round-trip self-check` line.

## Scope item 1 landed for Dict-valued generic classes (2026-11-18) — verification-pending

`register_erased_method_params_v1` / `register_erased_dict_class_v1`
(`50.mir/_MirLowering/module_lowering.spl`) publish, per instance method of a
generic class whose only `T`-bearing fields are `Dict<K, T>` values (K free of
`T`), which params are bare `T`; the flags ride the Err-shape text registry
(`mir_method_erased_params_key_v1`, key `<link>#erased-t-params`, class marker
`<Class>#erased-dict-class`) because the param-type registries reject a
TypeParam-bearing list. `erased_method_param_types_v1` (`expr_dispatch.spl`)
turns them into `Any` slots for the `InstanceMethod` call arm, so
`lower_method_call_arg` boxes the argument (`rt_value_int_wide`) like any Any
slot. Acceptance `generic_method_erased_i64_boundary_spec.spl` 3/3 GREEN (tag
dropped); prevention `generic_method_erased_field_roundtrip_spec.spl`.

Deliberately NOT done (and why): a bare `T`, `T?` or `[T]` FIELD class is
excluded. Probe: `Cell<T>{v: T}.set(x)` with the encode on stores the tagged
word while concrete `c.v` reads raw, i.e. x8 (a regression of a currently
coherent raw/raw path). Items 2 (caller decode of `T?`/`Result<T,E>`/bare `T`
returns) and 3 (encode at construct sites, decode at concrete field reads)
are still required before those shapes can be encoded. Named arguments to such
methods and the unresolved-owner recovery arm keep the old raw behaviour.
Native verification still needed (no native build was run).

Gate (after the 2026-11-18 IR trace review): the encode applies only when (a)
every `T`-bearing field of the class is a `Dict<K, T>` value, (b) no method of
the class returns `T`/`T?` other than inside `Result<T, E>` (`Bag.take -> T`
decodes then RE-ENCODES its tail and no caller decodes it, so encoding the
store would read back x8 — scope item 2), (c) the argument is a plain i64/u64
(text/records/bool/narrower ints keep their old representation), (d) no named
arguments. The production `AttributeStoreV1<T>` (`slots: [T?]` + `owner`
fields) is therefore NOT affected by this change; the `AttrI64StoreV1`
workaround stays. A `Result<T, E>` read (`Store.get`) was traced balanced: one
`rt_value_as_int_wide`, key encodes only, payload raw into `Ok`.

## Caller return-type instantiation + `T?` exemption landed (2026-11-26)

1. **`module_lowering.spl` (`register_erased_method_params_v1`)**: exempted
   `HirTypeKind.Optional(_)` alongside `HirTypeKind.Result(_, _)` from
   `#erased-ret-veto` (`-> T?` tails only normalize Option handles via
   `ensure_option_handle` and do not re-box decoded words; bare `-> T` remains
   vetoed so `generic_method_erased_field_roundtrip_spec.spl` stays coherent).
   Also registered generic `class` type parameter names under bare, layout, and
   canonical keys (`module_lowering.spl` & `declaration_providers_v1.spl`).
2. **`expr_dispatch.spl` / `method_calls_literals.spl` / `switch_operators_calls.spl`**:
   added `instantiate_method_return_hir_v1` / `remember_method_call_hir_return_v1`
   and wired them into `InstanceMethod`, `Unresolved`-resolved method, and
   `enum_match_expr_type` (`MethodCall`) arms so generic-class callers substitute
   receiver `Named(_, args)` type arguments (`Store<i64>.get` -> `Result<i64, text>`,
   `Store<i64>.get_opt` -> `i64?`, `Box<i64>.get` -> `i64`) and stop double-decoding
   (`>> 3` / `>> 6`) already-decoded payloads or raw `Box<T>` field returns.
3. **`AttrI64StoreV1` (`attribute_schema_v1.spl:300`)**: `KEPT-WITH-REASON`
   (`mixed_raw_slots_owner_and_tagged_dict_hash_in_AttributeStoreV1`).
   `AttributeStoreV1<T>` mixes `AttrOwnerV1<T>?` + `[T?]` (raw scalar payloads)
   and `hash: Dict<i64, T>` (tagged `RuntimeValue` words needed so raw `3` does
   not alias `rt_dict_get`'s `TAG_NIL` miss sentinel); without specialization, no
   single caller scalar ABI can serve both placements simultaneously. Also
   referenced by `src/compiler/10.frontend/core/_AstExpr/nodes.spl`.

## Uniform `T?` payload in `AttributeStoreV1<T>` + `@workaround` retirement (2026-11-26)

1. **`attribute_schema_v1.spl`**: changed `AttributeStoreV1<T>.hash` from
   `Dict<i64, T>` to `Dict<i64, T?>` (`self.hash[node] = Some(value)` and
   `match self.hash[node]: case Some(v): return Ok(v)`). Because every `Some(value)`
   is a `TAG_HEAP` `RtCoreEnum` handle holding the raw scalar/payload word (and
   never collides with `rt_dict_get`'s `TAG_NIL == 3` miss sentinel or triggers
   `rt_value_as_int_wide` `>> 3`), `Embedded` (`AttrOwnerV1<T>?`), `Column`
   (`[T?]`), `ArrayIndex` (`[T?]`), and `SparseHash` (`Dict<i64, T?>`) now all
   share the exact same raw-payload `class_erased_raw_slot_flags_v1` (`08ce3f6bb79`)
   + `instantiate_method_return_hir_v1` (`#11865`) ABI across `9000000000`, `7`,
   `-5`, `3`, `0`, and `nil`/absent.
2. **`nodes.spl` & `@workaround` retirement**: switched `expr_attr_extra_stores`,
   `expr_attr_op_stores`, and `expr_attr_i64_round_trips` back to
   `AttributeStoreV1<i64>` (`attr_store_detached_v1<i64>`). Retired
   `# @workaround bug=native_erased_generic_optional_return_2026-11-15` from
   `attribute_schema_v1.spl` and `attribute_layouts_spec.spl` (keeping
   `AttrI64StoreV1` as an optional non-generic concrete `i64` store without the
   `@workaround` marker). Updated `wa_src_lane4_workaround_audit_spec.spl`,
   `attribute_layouts_spec.spl`, and `generic_method_erased_i64_boundary_spec.spl`.

## WA-P3 Addendum: Bare `-> T`, Field/Param Bitcast Coherence, and Unannotated `.poll()` (2026-11-26)

- **Scope Item 2 (`Bag<T>.take -> T` on `#erased-dict-class`)**:
  - Removed the `#erased-ret-veto` short-circuit in `erased_method_param_types_v1` and `instantiate_method_return_hir_v1` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`), and decoded `#erased-dict-class` bare `-> T` call results once via `decode_runtime_value` in `coerce_erased_bare_method_result_v1` while keeping non-Dict class-erased containers raw/bitcast.
- **Generic Class Field Store/Read and `CellF<f64>` / `Box<f64>`**:
  - `src/compiler/50.mir/_MirLowering/function_lowering.spl` and `expr_dispatch.spl` (`lower_return_expr`): skip `mark_runtime_value_local` on bare `TypeParam` parameters and `box_runtime_value` on bare `TypeParam` returns inside non-Dict/non-array/non-slice bare-`T`/`T?`-field class-erased containers (`is_class_erased_container_fn_v1`), keeping raw/bitcast `i64`/`f64` coherent with `Box.put`/`Cell.set`/`c.v = ...`.
  - `src/compiler/50.mir/_MirLowering/module_lowering.spl` (`register_local_generic_method_params_v1`): populate parameter defaults for single-module `lower_module` generic methods so `CellF<f64>.set(2.5)` bitcasts even without `register_fn_prescan`.
  - `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `mir_lowering_stmts.spl`, and `switch_operators_calls.spl`: recover cross-module `provider_method_row_keys` return signatures (`semantic_call_hir_return_type_v1`), mark non-Dict `Optional(TypeParam)` returns and field reads with `native_trait_concrete_option_locals`, adapt concrete `SetField` / `StructConstruct` bare `TypeParam` field writes (`adapt_class_erased_field_store_v1`), and prevent argumentless/erased `Named(_, [])` or `TypeParam` locals/expressions from shadowing concrete `Named(sym, [...])` receiver types.
- **Related `20.hir` Unannotated Enum-Match Owner Propagation**:
  - Updated `src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl`, `expression_core.spl`, and `statements.spl` for unannotated `val fut = Future.from_value(task()); match fut.poll(): case Poll.Ready(v):`, chained `match Future.from_value(task()).poll():`, and unannotated `match` bindings (`TaskPollResult.Ready(outcome)`).
- **Note on out-of-scope backend behavior (`60.mir_opt`/`70.backend`)**: an `f64` `BinOp` temporary live across a later branching call gets slotted by `ssa_alloca_transform_blocks` with a fresh local ID absent from `fn_.locals`, causing `get_local_type` to fall back to `i64`; kept out of scope for this `50.mir` fix.
