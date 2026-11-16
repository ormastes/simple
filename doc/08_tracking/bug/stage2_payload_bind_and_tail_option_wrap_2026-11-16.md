# Stage 2: `-> T` bodies return `Some(T)`; generic-enum payload/unit binds (2026-11-16)

Status: defect A FIXED in source (`2498a42ee19`, seed MIR spec red 0/2 ->
green 2/2), native confirmation pending the next integration Stage 2 build.
Defects B (`24229da9238`) and C (`5deef7d3d5c`) FIXED in source, seed-verified;
explicit `return <T?>` from `-> T` fixed (`29ec0f8506e`). Native pending.
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

### Root cause

The earlier reading here (the `fd5056ec44e` tail override answering
`Optional`) was wrong: that override only threads the type for `-> T?`, and a
`-> LocalId` body is lowered by plain `lower_block`.

The real cause is the tail conditional's join. `lower_expr_impl(expr) ->
LocalId` (`_MirLoweringExpr/expr_dispatch.spl`) ends in a match over
`HirExprKind`. Its CfgSelect and InlineAsmMatch arms call `-> LocalId?`
methods (`lower_cfg_select` / `lower_inline_asm_match`,
`_MirLowering/asm_and_targets.spl:114/412`), so the whole match joins to
`LocalId?`. Two producers then turn the result into a handle:
- Typed HIR (the Stage 2 build): `lower_expr_impl`'s own MatchCase arm
  (`expr_dispatch.spl:8029`, pinned 8448) passes `expr.type_` (`LocalId?`) as
  the expected type, and `lower_block_expected` runs `ensure_option_handle` on
  every arm (`function_lowering.spl` around line 2028). That is the IntLit-arm
  `rt_enum_new` site gdb found.
- Untyped HIR (the seed spec pipeline): `join_untyped_optional_arms`
  (`mir_lowering_stmts.spl:4149`) normalizes the merged word to `T?`.

Either way `lower_function` returned the `Some` handle where `LocalId` is
declared.

Small repro (`test/fixtures/native_tail_match_optional_arm_plain_return/main.spl`):
a `me lower_impl(k) -> Lid` whose tail match has one `self.lower_sel(n)` arm
(`-> Lid?`). Seed `L 11 12 13`; Stage 2 cranelift and llvm `L 4 4 4`.

### Fix (`2498a42ee19`)

`lower_function` narrows a tail whose lowered local is `T?` when a
record/text/collection `T` is declared. It emits `rt_unwrap_or_trap` (None
aborts) and decodes the payload with `decode_declared_enum_payload_slot`
(`option_payload_for_plain_sink`, `switch_operators_calls.spl`). Int is not a
sink: `SIMPLE_BOOTSTRAP=1` erases `T?` to Int.

Guard: `test/01_unit/compiler/mir/tail_match_optional_arm_into_plain_return_spec.spl`.
On the seed it is red 0/2 without the fix and green 2/2 with it.

Source workaround for the real site (`d648234f1fb`). It needs no Stage 2
rebuild and can be cherry-picked into the stage3 workaround lane. In
`lower_expr_impl`, both arms now coalesce with
`?? self.builder.new_temp(MirType.unit())`, which is the fallback
`lower_cfg_select` already uses. The match no longer joins to `LocalId?`.

When the trap can fire (the effect of `2498a42ee19`):
- `lower_cfg_select` never returns None; every path returns a temp.
- `lower_inline_asm_match` returns None only after `error_fatal`, or for an
  asm-match arm that has no asm body (`asm_and_targets.spl:487/526`).
- Compiler source contains no `asm match`.

Still open:
- Perf and memory: until the workaround is in a Stage 2,
  `lower_expr_impl` allocates an Option box per call on the hottest MIR path.
  With the generic fix alone, it also pays an unwrap per call. Under no-GC
  that box is plausibly a leak.
- Generic alternative, not done: thread the declared `T` into the arms. It is
  held back because it changes every struct-returning conditional tail, and
  only a full Stage 2 rebuild can validate that.
- `SIMPLE_BOOTSTRAP=1` gap:
  - With erased HIR, the `pick(n)` arm's call returns `(Bool, I64)` and the
    join is a plain copy, so MIR has no `T?` evidence and the narrow does not
    fire. Measured: `lower_impl`'s Return is `Copy 3`, and the Sel arm
    returns pick's handle.
  - The Stage 3 build that miscompiled used the typed path (the gdb trace
    shows the per-arm `ensure_option_handle`).
- Explicit `return <T?>` from `-> T`: fixed, see below.
- The census SEGV sites are not shown to be this class.
  `binding_kind_type` (`20.hir/hir_lowering/statements.spl:112`) returns
  through explicit `return X ?? unknown`, not through a tail join. Re-census
  them on the next Stage 2.

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

None of these shapes has a `T?` arm in a `-> T` tail, which is why they did
not reproduce. The f10 shape above does.

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

Root cause:
- The single-binder enum arm (`switch_operators_calls.spl`, around line
  5106) decodes the payload through the declared slot `T`.
- The substitution to `Lid` (around line 5130) only remembers the HIR type.
- Field access resolves its owner through `struct_value_syms`, which only the
  Named decode sets.
- So `item.id` lowered to a `GetField` with a Unit dest. The arm copied
  nothing into the match result, as seed MIR shows.

Fix (`24229da9238`): when the declared slot is a TypeParam and its
instantiation is Named, re-run `decode_declared_enum_payload_slot` with the
instantiated type. For a record word this emits no instruction; it only tags
the owner. Scalar instantiations keep the `T` decode.

Guard: `test/01_unit/compiler/mir/generic_enum_record_payload_field_bind_spec.spl`,
seed 0/1 without the fix and 1/1 with it. The multi-binder path (around line
5315) is not changed.

## Defect C: generic user-enum unit variant fails the identity check

Fixture: `test/fixtures/native_generic_enum_unit_variant_match/main.spl`

`Box.Empty` (from `val e: Box<text> = Box.Empty`) panics with "total enum match
fell through on 'Box'" on both backends. The seed prints `D <empty>`.

Root cause, measured with gdb on the integ2 Stage 2 compiling the fixture:
- `Full` goes through `lower_enum_construct_named("main.Box")`, then
  `enum_runtime_id` takes the qualified branch and returns `0x69610c43`
  (`hm_hash("main.Box")`). That is correct.
- `Empty` goes through `lower_enum_construct_named("Box")`, then the bare
  branch `val found = index.get(k); if found != None: return found`. It
  returned `0x2af1b71`, which varies per run.
- The Stage 2 code for that `return found` is `rt_value_unbox_int(<Option
  handle>)`, not an unwrap.
- Release MIR lowering of the same shape unwraps with `rt_unwrap_or_trap`
  in both HIR modes on the seed. The miscompile is in the shipped Stage 2,
  so it is fixed at the source.

Fix (`5deef7d3d5c`): `enum_runtime_id` reads the bare map with `has()` and
an index, as its own comment already requires. Census twin: `da943b32365`
(`bitfield_type_sym_for`). Native red/green needs the Stage 2 rebuild; the
seed already printed the right answer.

## Explicit `return <T?>` from `-> T`

`fn direct(n) -> Lid: return pick(n)` returned pick's Option handle. Fix
`29ec0f8506e` applies the tail narrow in `lower_return_expr`:
`rt_unwrap_or_trap`, so None aborts and nil is never widened. Seed spec goes
from 3/4 to 4/4.

## Census of compiler source (2026-11-16, awk heuristic)

| class | hits |
|---|---|
| `-> T` whose tail `match`/`if` has an arm ending in a call to an unambiguously named `-> T?` function | `lower_expr_impl` only (CfgSelect and InlineAsmMatch arms, workaround `d648234f1fb`) |
| `val x = d.get(k)` ... `return x` from a non-optional return | `enum_runtime_id` (`5deef7d3d5c`) and `bitfield_type_sym_for` (`da943b32365`) |

- Validation: on the pre-workaround tree (`d648234f1fb~1`), the tail
  heuristic finds the two known `lower_expr_impl` arms.
- False positives, inspected and excluded: 3, all `val x = if ...` bindings.
- Not covered: arms that are a `T?` local, arms calling ambiguously named
  functions, and the `SIMPLE_BOOTSTRAP=1` shape.

## Separate, noted only

Calling a class `fn` (static) as `Gen.st_first(..)` refuses at MIR with
`unresolved method call: st_first route=static-nominal`. Calling it through an
instance (`g.first_or(..)`) mis-binds the receiver as the first argument.
