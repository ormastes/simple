# Phase 2 miscompile: `-> T` return of an if-val binder over `tuple_at<T>(..)` int-boxes the record handle

- **Status:** FIX LANDED IN SOURCE (2026-11-24); end-to-end NOT verified
  (needs the Phase 2 compiler rebuilt from this source, hours)
- **Component:** `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`
  (`declared_exists_check_type`), consumed by the MIR ExistsCheck arm
  (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:8289`) and the
  `-> T` return arm (`expr_dispatch.spl:4596`, `lower_return_expr`)
- **Found:** 2026-11-24, release/1.0.0 pin `0285176e3a7b`, Windows MSVC,
  `native-build --backend llvm --runtime-bundle core-c-bootstrap`; the Phase 3
  compiler (built by Phase 2) crashes in `MirLowering.lower_index_expr`
- **Trigger commit:** `37f7c2b6d8e` (PR #10930, 2026-11-23, "substitute
  turbofish direct-call returns")

## Symptom

A generic function

```simple
fn get_req<T>(tuple: i64, index: i64) -> T:
    if val present = compiler_value_tuple_at<T>(tuple, index):
        return present
    panic("absent {index}")
```

returns the record payload **int-boxed** when `T` is a struct: the heap
pointer shifted left by 3 (tag bits 0). The caller treats the word as a
pointer and dereferences garbage (AV / rc=139).

Evidence: Phase 3 `lower_index_expr_from_hir`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4694-4702`) reads
`base`/`index` through `_sffi_tuple_get_req<HirExpr>` (`expr_dispatch.spl:84-87`);
cdb showed `base = 0x114680a96b80 == 0x228d0152d70 << 3`.

## Repro (pinned source, Phase 2 `stage2-admitted/simple.exe`)

`/c/dev/simple-rb5/build/bootstrap/pinned-src/pinned-0285176e3a7b/build/probe/`,
built with `bash .../build/rboot/p3-inproc-rb5.sh build/probe/<f>.spl <name>`:

| file | shape (`-> T` body) | result |
|---|---|---|
| `tg_a.spl` | `if val present = compiler_value_tuple_at<T>(..): return present`, `@always_inline` | **SEGV rc=139** |
| `tg_b.spl` | helper returns `T?`, `if val` at the concrete call site | prints `B 9` |
| `tg_c.spl` | `match` destructuring at the call site | prints `C 7 9` |
| `tg_d.spl` | `match compiler_value_tuple_at<T>(..): case Some(p): p / case None: panic` | **SEGV rc=139** |
| `tg_e.spl` | as `tg_a`, no `@always_inline` | **SEGV rc=139** |
| `tg_f.spl` | `val slot: T? = compiler_value_tuple_at<T>(..)` then `if val present = slot: return present` | prints `X 7` |

## Root cause

`if val present = <call>` is parser-desugared to `present = <call>.?` plus
`present != nil`; the binder's HIR type comes from
`HirLowering.declared_exists_check_type` (`expression_core.spl:456`).

Before #10930 every `HirExprKind.Call` source set `callable = callee`, so the
binder got the callee's **declared** return `TElement?`
(`Optional(TypeParam)`). #10930 made the turbofish branch exclusive:

```simple
if applied_args.len() > 0:
    if val inst_ret = self.instantiated_direct_call_return_kind(source.kind):
        source_type = inst_ret
else:
    callable = _hir_expr_symbol_or_invalid(callee.kind)
```

Inside a generic body the actual is the enclosing binder `T`, which lowers to
`HirTypeKind.TypeParam`; `substitute_declared_pattern_type` yields
`Optional(TypeParam)`, `declared_pattern_slot_type_is_concrete` rejects it,
`instantiated_direct_call_return_kind` returns `None`, and **no fallback runs**.
The ExistsCheck is left untyped (`Error`).

In MIR (`expr_dispatch.spl:8289` ExistsCheck arm) an untyped result slot is a
bare `I64`, nothing marks it as a runtime value (the payload-type switch has
no `TypeParam` arm, and `option_payload_or_self`'s fresh `rt_unwrap_or_self`
local carries no mark). `lower_return_expr`'s
`case HirTypeKind.Any | HirTypeKind.TypeParam` (`expr_dispatch.spl:4596`)
then calls `box_runtime_value`, whose `I64` arm emits
`rt_value_int_wide(word)` — the record pointer becomes `ptr << 3`.

Why the typed form (`tg_f`) works: the `val slot: T?` annotation gives the
ExistsCheck `Optional(TypeParam)`, `lower_type` makes the slot
`Tuple(Bool, I64)`, and `box_runtime_value` passes a Tuple-typed local
through untouched. That is exactly the pre-#10930 behaviour for `tg_a`, and
what the fix restores. (`tg_f` is the **source-side workaround** for code
that must compile with the broken pin: bind the call to an explicitly typed
`T?` local first.)

In-process confirmation (seed interpreter, `parse_and_build_module ->
HirLowering -> MirLowering`, `SIMPLE_BOOTSTRAP=1`): before the fix `get_a`
MIR contains `rt_value_int_wide` with the binder local typed `I64`; after
the fix it does not, and the `val slot: T?` twin never did.

## Fix

`src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`,
`declared_exists_check_type`: always take the callee as the fallback
`callable`; a concrete turbofish instantiation still wins (and clears the
fallback). Shortest diff, no new abstraction:

```simple
case HirExprKind.Call(callee, _, call_type_args):
    callable = _hir_expr_symbol_or_invalid(callee.kind)
    val applied_args: [HirType] = call_type_args
    if applied_args.len() > 0:
        if val inst_ret = self.instantiated_direct_call_return_kind(source.kind):
            source_type = inst_ret
            callable = SymbolId(id: -1)
```

Spec: `test/01_unit/compiler/mir/generic_if_val_turbofish_erased_binder_spec.spl`
(asserts no `rt_value_int_wide` in `get_a`, its `@always_inline` twin and
the `val slot: T?` form; a concrete record caller has no
`rt_value_as_int_wide`; a concrete `tuple_at<R>` if-val outside a generic
body still substitutes).

Also in the same change: `src/compiler/20.hir/return_type_interface_v1.spl`
`rti_symbol_module` made `pub` — it is imported by
`50.mir/_MirLowering/function_lowering.spl` (since `ac1fd826bf4`,
2026-11-23) and the seed interpreter hard-fails every in-process MIR spec on
this tip with `semantic: private fn rti_symbol_module ... is not visible`.

## Not fixed here (pre-existing, separate)

- **`tg_d` (`match .. case Some(p): p` tail in a `-> T` body)** still
  int-boxes (`get_d` in the probe: `rt_value_int_wide` present before and
  after this fix). #10930 did not touch match scrutinees; the 11-19 record
  (`stage2_generic_tail_unwrap_reboxes_record_2026-11-19.md`, "Not done")
  already lists the `match v: case Some(x): x` tail as unaddressed. The
  erased `Some(p)` payload binder is an unmarked raw word in MIR match
  lowering; marking it a runtime value is wrong for a raw-int `T`
  (`tuple_at` forwards RAW tuple words — the known-ambiguous shape pinned by
  `generic_tail_unwrap_record_spec.spl`). Needs its own decision.
- `expression_core.spl:428-436` (`named_owner_for_hir_type` for a turbofish
  Call) has the same exclusive shape (`return -1` when the instantiation is
  not concrete); for an erased `T?` owner the fallback would also be `-1`, so
  it is left alone but named.

## Verification status

- In-process specs (seed interpreter, Windows): new spec 6/6 PASS; #10930's
  `test/01_unit/compiler/50.mir/generic_turbofish_call_return_subst_spec.spl`
  3/3 PASS (the substitution success path is unchanged); 11-19's
  `test/01_unit/compiler/mir/generic_tail_unwrap_record_spec.spl` 9/9 PASS
  (the `.unwrap()` tail of the raw-tuple forwarder keeps its box).
- **Not verified end to end:** `tg_a`/`tg_e` running correctly requires the
  Phase 2 compiler rebuilt from this source (hours). The bootstrap was not
  run in this change.
