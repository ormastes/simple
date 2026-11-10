# native_method_call_hir_lowering_invalid_array_handle_2026-11-07

- Severity: P0 (phase-4 blocker; ~775 `unresolved method call` errors in batch
  q0023 alone, log `C:/dev/p3new/s4/out/s4e_q/q0023/native-build.log.err`)
- Status: fix-implemented-verification-pending
- Found on: stage3 `s3_fable54m`, `s3_fable56`, `s3_fable57s`, `s3_fable59`

## Repro

`C:/dev/p3new/s3sanity/root/test/s3sanity/vb_mm1.spl`:

```
struct Custom:
    value: i64

impl Custom:
    fn get() -> i64:
        self.value

fn main() -> i64:
    val custom = Custom(value: 7)
    if custom.get() == 7:
        print "PASS vb_mm1"
    0
```

`pwsh -NoProfile -File C:/dev/p3new/s3sanity/run_case_dir_mf8.ps1 -Name vb_mm1 -Bin <stage3> -Tag <tag>`
prints, between `point=entry` and `point=post-lowering`:

```
[simple-runtime][error] rejected invalid array handle before dereference; probable compiler/FFI ABI mismatch (value_bits=0x...)
MIR lowering error: unresolved method call: get route=runtime-fallback key=test.s3sanity.vb_mm1.Custom::get ... lookup_method_in_type=no
```

Control `vb_mm2.spl` (same struct/impl, `main` only prints) passes; free-function
calls (`fn1.spl`) pass.

## Root cause (captured under lldb)

The work runs in the worker child (`s3 run src/app/cli/native_build_worker.spl ...`,
`SIMPLE_NATIVE_BUILD_WORKER=1`). Breaking on the inlined report sites in the
worker, the rejection is:

```
#0 rt_array_len
#1 compiler.frontend._FlatAstBridge.convert_nodes.convert_decl_fn + 2734
#2 compiler.frontend._FlatAstBridge.convert_nodes.convert_decl_method_fn
#3 compiler.frontend._FlatAstBridge.module_assembly.flat_ast_to_module
#4 ...module_assembly.parse_and_build_module_with_scope_owner
#5 ...module_assembly.parse_and_build_module_scoped
#6 compiler.frontend.frontend.frontend_parse_or_restore
#7 ...parse_full_frontend_preprocessed_with_scope
#8 ...parse_full_frontend_with_scope
#9 ...parse_full_frontend_stage4_streaming
```

The array passed to `rt_array_len` is the module global
`g_compiler_frontend__FlatAstBridge_convert_nodes__g_pending_defers`, read by
`val saved_pending_defers: [[Stmt]] = g_pending_defers` at the top of
`convert_decl_fn`.

`convert_decl_fn` swapped that process-lifetime global: copy it into
`saved_pending_defers`, `g_pending_defers = []`, and at the end
`g_pending_defers = saved_pending_defers`. Under the stage-4 streaming parse
the whole parse runs inside `rt_transient_array_scope_begin/end`, and every
array allocated in the scope is stamped and reclaimed at scope end. Both the
`[]` and the copy are such arrays, so after the first parse the global holds a
reclaimed handle, and the next `convert_decl_fn` (here an `impl` method)
dereferences it. This is the same class as
`ast_arena_reset_inside_transient_scope_2026-08-01` (fresh process-lifetime
arrays allocated inside the scope).

Not a stage2 miscompile and not the C runtime: the seed interpreter has no
transient scope, and #7376/#7378 (argv weak-tie owner in the hosted bundle)
change a different rejection source. `native_struct_i64_field_ctor_reads_wrong_value_2026-11-05`
has no array rejection and is unrelated.

## Fix

`convert_decl_fn` mutates the stack in place: record
`pending_defer_base = g_pending_defers.len()` (published as the scalar
`g_pending_defer_base` for `defer_return_replay` and the `STMT_RETURN` arm),
and truncate back to that length at the end. The global is never reassigned,
so no scope-stamped array is stored in it.

## Tests

- Repro / guard: `test/01_unit/compiler/frontend/pending_defers_transient_scope_spec.spl`
  (3/3 FAIL before, 3/3 PASS after).
- Existing: `test/01_unit/compiler/parser/defer_spec.spl`,
  `test/01_unit/compiler/frontend/pending_defer_state_take_install_spec.spl` PASS.
- Native verification pending: rerun vb_mm1 on the next stage3 leaf that folds
  `compiler.frontend._FlatAstBridge.convert_nodes`.

## Follow-up

`pending_defer_state_take` still does `g_pending_defers = []`; it is safe only
while it is never called inside a transient scope.

## Residual after #7506 (vbmm3 lane, 2026-11-07)

Leaf 61 (`s3_fable61`) shows 0 invalid-array-handle lines, but vb_mm1 still fails with
`unresolved method call get ... struct_method_syms=yes lookup_method_in_type=no`, and probe
vbx_a fails with E-RTI-006 "two rows for callee 'main'" whose stored owner text is the bytes of
the next `log_build_progress` line (`build] phase=mir state=running unit_kind=modules ...`).

Root cause: the leaf fold base (`25fede3cb71`) predates `d05dc7079db`. `MirLowering.rti` is a
class created before the scoped struct prescan (`driver_pipeline_lowering.spl:1252`), so promoting
`[self.rti]` does not walk its Dict children; `rows_by_module` / `rows_by_key` / `aliases` were
filled by `prescan_module_functions_v1` inside that scope and freed by
`driver_mir_inventory_scope_end_v1`. Release already carries `d05dc7079db`; the leaf needs the
three-root fold `C:/dev/p3new/s3new/p63_vbmm1.diff`.

Sibling audit (same class, release): `provider_default_literal_consts_v1` / `_owners_v1` are
filled inside a module scope (provider_metadata.spl:545-567), never refilled because the owners
set says done, and were not promote roots. Added. The only class-typed MirLowering fields are
`rti` and `symbols`; every child of both is now a root (gated by
`test/01_unit/compiler/mir/transient_owner_promotes_every_field_spec.spl`, which was red on
release before this fix and green after). `struct_method_syms` is retired and rebuilt per module
inside the module scope, so it is not a cross-scope survivor.

## Gate reconciliation and remaining verification (2026-11-10)

At release source `6d496f82c5a`, the MIR boundary gate rejected the correctly
promoted RTI child roots because its derived inventory omitted
`ReturnTypeInterfaceTable`. It also expected the older abort helper without
`bootstrap_mir_store_discard_pending()`, so it misreported six error exits as
unpaired. The guard now derives RTI children from their declarations and requires
pending bootstrap rows to be discarded before reverse-owner abort and scope end.

Root coverage compares exact field-path sets. Repeated promotion of the same
field does not add coverage or hide a missing/extra field. The owner grammar still
allows only the known promotion helper, and that helper must promote and free
each temporary wrapper. The runtime promotion-share contract
(`src/runtime/runtime_native.c`, promotion-share comment) preserves the same
promoted object set across repeated unchanged roots. Positive duplicate-root and
negative duplicate-without-free fixtures check these independent invariants.

After those scanner corrections, the real source still fails the inventory
check: `builder.module.attr_sites`, `target_context.build_profile`,
`target_context.subarch`, and `target_context.cpu_tier` are declared fields but
absent from `promote_transient_owner`. These are an actual inventory gap, not a
reason to loosen the guard. Their source repair and native qualification are
tracked separately from the scanner correction.

The canonical original-form native fixture is
`test/fixtures/compiler/native_unresolved_owner_method/struct_method.spl`. It
now returns nonzero when `custom.get()` produces the wrong value, instead of
silently returning zero without printing the expected marker. Qualification
requires the selected new compiler's native-build command to succeed and its
output executable to return zero and print `PASS vb_mm1`, with no invalid-array,
unresolved-method, or E-RTI-006 diagnostics. Historical manual relinks and the
source guard do not establish that outcome. This bug remains verification pending.
