# Stage 2: `-> T` bodies return `Some(T)`; generic-enum payload/unit binds (2026-11-16)

Status: OPEN. Root cause of defect A is localized to one decision in Stage 2's
MIR lowering. The trigger for the wrong decision is context dependent and still
unknown. Defects B and C have committed red fixtures. No fix has landed.
Every native claim below needs the next integration Stage 2 build to confirm it.

Binaries:
- Stage 2: `simple-integ2-20261115/.../bootstrap-s2probe-integ2/stage2/aarch64-unknown-linux-gnu/simple`, sha256 `1b04422037a68ab6`, built from pinned source `8453e87c8767`.
- Stage 3: `boot-fable-lane-scripts/diaglink/s3i2/w-a/simple-r8`, built by that Stage 2 from `work/stage3-integ2-workarounds-20261116` (`af8d78ff282`) plus the fix objects and the transient-scope shim in `simple-r8.extras`/`.flags`.

## Defect A: Stage 3 LLVM IR, every operand is `%l4` / `%l<0x13_00000004>`

Repro: `var w: [i64] = [0, 1]; print "{w.len()}"`, compiled with `simple-r8 compile`.

The IR has correct dest ids. Every operand local is the same id, and every
string constant is `c"\00"`.

### Wrong reading, corrected

`0x13_00000004` is not `(disc<<32)|enum_id`. It is word 0 of an `RtCoreEnum`
(`runtime_native.c:1533`): `kind = RT_VALUE_HEAP_ENUM (4)` plus
`transient_scope_id << 32`.

The r8 binary links the transient shim, so the scope id there is 0 and the
operand prints as `%l4`. r8ns, without the shim, gives scope `0x13`.

The backend's `case Copy(local)` bind is correct. Disassembly of
`MirToLlvm.translate_operand_at` shows `rt_enum_payload(kind)` followed by
`local_id_value`.

`mir_operand_copy(local)` deep-copies its by-value `LocalId` argument by
loading word 0. Its callers hand it an Option box instead of a `LocalId`.

### gdb evidence (r8, j4)

A conditional break on `mir_operand_copy` fired where `*(u8*)(arg&~7) == 4`.
There were 6 hits, from `aggregate_literal_operand`, `emit_interpolation_segment`,
`lower_string_interpolation`, `coerce_concat_operand` and
`lower_bootstrap_print_call`. Box contents:
- `enum_id=1, disc=0`, payload a heap `LocalId`: Option.Some(LocalId).
- `enum_id=0, disc=0`, payload a small tagged int. This is a downstream product of `box_runtime_value` receiving the Some box.

A FinishBreakpoint bisect checked return values. `MirBuilder.new_temp` returns
a correct `LocalId`. `MirLowering.lower_expr_impl` returns
`Some(LocalId)` (enum_id 1). So does `lower_expr`, which passes it through.

A `rt_enum_new(1, 0, x)` break whose caller frame is `lower_expr_impl` lands
at static `0x42b564`. That site sits in the IntLit arm, right after
`emit_const` and the `int:done` trace print:

```
result -> rt_enum_id(result) == 1 ? result : rt_enum_new(1, result == 3, result)
```

This is `classify_option_word(local, _, sentinel_is_nil=true)`, reached as
`normalize_option_handle` from `ensure_option_handle`
(`switch_operators_calls.spl:727-782`, pinned source).

### Root-cause location (Stage 2 = pinned 8453e87c8767 source)

`lower_function` (`_MirLowering/function_lowering.spl`, about line 1110)
replaces `tail_return_type` with
`resolved_call_hir_return_type(fn_.symbol)` whenever that call answers
`Optional`. This came from `fd5056ec44e`, and the explicit `return` path
(`lower_return_expr`) reads the same function.

The body is then lowered by `lower_block_expected(fn_.body, tail_return_type)`.
The tail match's arms (`lower_block_expected` at about line 2028) run
`ensure_option_handle(local, found_expected)`. So every arm value of
`me lower_expr_impl(expr: HirExpr) -> LocalId` is wrapped into `Some`. The
function returns that word as a plain `LocalId`.

The same shape explains the coordinator's census crash sites:
- `cc_is_char_type` <- `char_int_operand_is_char`
- `hir_binding_index_element` <- `binding_kind_type`

These are `-> HirType` functions whose returns arrive as boxes.

Not ruled in yet: why `resolved_call_hir_return_type` answers `Optional` for a
`-> LocalId` method in the Phase 3 context. Its sources, in order:
1. `fn_return_types`. It is never written, so it is always empty.
2. The symbol's `Function(_, ret, _)` type via `self.symbols.get_symbol_raw(fn_.symbol.id)`.
3. `module_fn_declared_returns`. It is cleared per module and holds only `module.functions`.
4. The name-keyed `bootstrap_fn_ret_hir_type_lookup(found_sym.name)`.

`lower_expr_impl`, `binding_kind_type` and `binding_payload_type` each have
exactly one definition in the tree. That makes a plain name collision in (4)
unlikely. A symbol-id / symbol-table mismatch in (2) under MIR shard workers is
the leading hypothesis. It is not verified.

### Fixtures that do NOT reproduce

All of these run on the same Stage 2 on cranelift and llvm, and all match the
seed interpreter:
- struct payload `case Copy(local)` in a free function, after a field load, and after an array-index load, in `me` methods
- text payload `case Str(v)`
- `Option<Option<T>>` matches
- `if val x = opt` then `var s = x`
- `opt ?? fallback` as a match-arm tail and inside a struct-builder method
- a `me lower_impl(k) -> Lid` with a tail match whose arms return `b.new_temp()`
- `-> Ty` with `return opt ?? unknown` and `if val t = ...: return t`

These were also run with the Phase 3 env (`SIMPLE_BOOTSTRAP=` empty,
`SIMPLE_NATIVE_ARENA_DECLS=1`, `SIMPLE_ABI_POLICY=v1`) and a warm HIR cache
(second build is a cache hit).

So defect A depends on the whole-program / MIR-shard context.

### Next step

Instrument `lower_function` to `eprint` `fn_.name`, the branch of
`resolved_call_hir_return_type` that answered, and the answer's kind whenever
it overrides a non-Optional `fn_.return_type`. Then recompile one module
(`expr_dispatch.spl`) through the Phase 3 replay (`diaglink/s3i2/one_module.sh`).
That needs a Stage 2 rebuilt with the eprint.

Fail-closed fix candidate, pending that evidence: only override when
`fn_.return_type` is the bootstrap-erased default (the case `fd5056ec44e`
targeted). A declared non-optional `Named`/struct return must never become
Optional.

## Defect B: generic user-enum struct payload bind loses the field read

Fixture: `test/fixtures/native_generic_enum_struct_payload_bind/main.spl`

`fn free_first(b: Box<Lid>) -> i64: match b: case Full(item): item.id`

| | output |
|---|---|
| seed | `A 33` |
| cranelift | `A 196570417711888` (the payload pointer) |
| llvm | `A 222204877299624` |

In the llvm disassembly, the Full arm calls `rt_enum_payload` and then returns
an uninitialized stack slot. `item.id` is never emitted into the result.

Suspect: `decode_declared_enum_payload_slot` decodes with the uninstantiated
`T` (`switch_operators_calls.spl` about line 5076). Substitution to `Lid`
(about line 5100) is metadata only.

## Defect C: generic user-enum unit variant fails the identity check

Fixture: `test/fixtures/native_generic_enum_unit_variant_match/main.spl`

`Box.Empty` (from `val e: Box<text> = Box.Empty`) panics with "total enum match
fell through on 'Box'" on both backends. The seed prints `D <empty>`.

## Separate, noted only

Calling a class `fn` (static) as `Gen.st_first(..)` refuses at MIR with
`unresolved method call: st_first route=static-nominal`. Calling it through an
instance (`g.first_or(..)`) mis-binds the receiver as the first argument.
