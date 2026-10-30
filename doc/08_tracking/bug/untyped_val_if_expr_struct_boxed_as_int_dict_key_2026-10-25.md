# Untyped `val x = if ..` struct binding is typed i64, so a Dict<Struct,_> key is int-boxed (Stage 3 B6)

- **Date:** 2026-10-25
- **Status:** workaround landed in source (module_build.spl); compiler fix OPEN (takes effect only when Phase 3 rebuilds itself)
- **Severity:** P0 for Phase 3 Stage 3 (hello world SEGV after HIR lowering)
- **Producer:** Stage 2 (p2shard-17), Cranelift aarch64

## Symptom

Stage 3 (`S/r27/bp/simple.p3b5`) SEGVs after HIR lowering in
`compiler.hir.generated.hir_codec.hc_enc_hir_module+37488`
<- `hir_module_encode_retained_v1` <- `lower_and_check_retained_owner_impl`:

```
ldr x9, [x27]                ; dk6 = ks6[i]
and x9, x9, #~7
ldr x9, [x9]                 ; SEGV, x9 = 0x5555572449088
```

The crash block is `for dk6 in ks6: val enc_node_v7: SymbolId = dk6`
(hir_codec.spl:4951-4952, the `HirModule.functions` key loop). The element is
`0x5555572449088 = 0xaaaaae489211 << 3`: a heap-tagged `SymbolId` handle that was
passed through `rt_value_int_wide`. `hc_order_symbol_id_keys_v1` moves elements
raw (rt_array_get / rt_array_push), so the boxed value came from the Dict itself.

## Root cause

`src/compiler/20.hir/hir_lowering/_Items/module_build.spl:571-572` (non-bootstrap
`lower_module` path):

```
val fn_key = if real_id.is_valid(): real_id else: SymbolId(id: lower_idx)
functions[fn_key] = hir_fn
```

Disassembly of `HirLowering.lower_module` (0x150b6b4..0x150b7c8): `is_valid` ->
if-merge -> `lsl #3` + `rt_value_int_wide(fn_key)` -> `rt_dict_set(functions, BOXED, hir_fn)`.
The bootstrap path (`val fn_key: SymbolId = hir_fn.symbol`, annotated) passes the raw
handle (0x15103e8, 0x1511b0c).

Stage 2 repro (local scratch, not committed; the committed spec carries the same functions: src/app/zz_p3b6/r.spl, r2.spl, compiled by `S/r27/stage2-simple`):

| form | extra `rt_value_int_wide` on the key | runs |
|---|---|---|
| `val k = if c: pick(n) else: K(id: 99)` (call arm) | yes | SEGV |
| `val real = pick(n); val k = if real.ok(): real else: K(..)` | yes | SEGV |
| `val k: K = if ..` (annotated) | no | ok |
| `var k: K = real; if not ..: k = K(..)` | no | ok |
| `val k = if c: K(..) else: K(..)` (both ctor arms) | no | ok |
| `val real: K = ..; val k = if real.ok(): real else: K(..)` | no | ok |

So the merge slot only keeps its struct identity when every arm carries the same
`struct_value_syms` name. An arm whose value comes from a struct-returning CALL
(directly or via an untyped `val`) does not agree with the constructor arm, so
`remember_merged_arm_identity` (mir_lowering_stmts.spl) leaves the merge slot with
no struct name. The untyped Let (`mir_type` = i64 for `Infer`) then has no
Struct arm in its `effective_type` chain and no `struct_sym`, so the binding is a
plain i64 local, and `box_runtime_value` (expr_dispatch.spl) boxes it as an
integer at `d[k] = v`.

Candidate compiler fixes (not built; Stage 2 is not rebuilt per policy):
1. `remember_merged_arm_identity`: when an arm has no `struct_value_syms` entry,
   derive its name from its MIR `Struct(sym)` type / call return shape, so the
   call arm and the ctor arm agree (and check why the call-result spelling differs
   from the ctor spelling).
2. Let lowering: add a `local_mir_type_of(init_local)` is `Struct` arm to the
   `effective_type` chain so an untyped struct binding never becomes i64.

## Census

`grep -E '(val|var) x = if .*else: *[A-Z]\w*\('` over src/compiler + src/app/cli: 10 sites;
only module_build.spl:571 is a struct used as a Dict key. The others (Option
`Some(..)`, `LocalId`, `HirType`, `Expr`, `MirType`) are not index-set keys, but
they share the binding mis-type and should be annotated if they ever fault.

## Workaround

module_build.spl:571 annotated `val fn_key: SymbolId = if ..` (tagged
`@workaround bug=untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25`).
Regression spec: `test/01_unit/compiler/50.mir/untyped_if_struct_dict_key_spec.spl`.
