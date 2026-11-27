# Stage 2 SIGSEGV in the surface projection on a fixed-size array field `[T; <int literal>]` (2026-11-13)

Status: root-caused and fixed in source (2026-11-13, work/segv-arrlit-20261113). A new
Stage 2 is the final proof; see "Root cause (resolved)" below. Original text:
open. This kills every run-26 HIR shard worker at `claimed=0` in
`compiler_cli_build`. It also kills the final native-build worker in process
(`exited with code -139`). This crash is the run-26 `signal=11`. The skeleton
parse error printed before it (`feature_caps_arch32.spl: 146:44`) is a separate
symptom of the skeleton bug fixed in 721ae44607d.

## Minimal repro (run-26 Stage 2 candidate `2f9dedc191f9`, aarch64)

`src/lib/archctx/arch_context.spl`:

    struct Ext:
        bytes: [u8; 4096]

`src/app/mini/main.spl`:

    use std.archctx.arch_context.{Ext}

    fn main():
        print "archctx"

Build this as a git checkout with
`native-build --source src/app --source src/lib --entry-closure --entry src/app/mini/main.spl`.
Add `SIMPLE_SHARD_SMALL_CLOSURE_MAX=0` to get a HIR shard worker. Without it,
the in-process final worker crashes the same way. A run takes about 9 s in a
12 GiB scope.

| field | result |
|---|---|
| `bytes: [u8; 4096]` (int literal) | SIGSEGV |
| `bytes: [u8; N]` with `val N: i64 = 4` | ok |
| `bytes: [u8]` (unsized) | ok |
| full `src/os/kernel/arch/arch_context.spl` | SIGSEGV (the run-26 site) |

## Backtrace (replayed worker under gdb)

    #0 ast_semantic_value.ast_semantic_encode_expr      pc 0x886e00 / 0x886e18
    #1 ast_semantic_value.ast_semantic_encode_type
    #2 module_surface_semantic_projection._surface_type_digest
    #3 module_surface_semantic_projection._surface_field
    #4 module_surface_semantic_projection.module_surface_semantic_projection
    #5 module_surface_declarations.module_surface_from_owner
    #7 ModuleSurfaceBuilder.add_parsed_canonical
    #9 driver_source_parse_retained CompilerDriver.parse_all_retained_observation_v1

The faulting instruction is `ldr x10, [x1, x14, lsl #3]`. It is an indexed
payload load whose data pointer (`[x21, #24]`) is not a valid address. That
fits reading the `IntLit(i64)` payload of the `Expr` held in
`Type.Array(Type, Expr?)`. Suspect: `src/compiler/10.frontend/generated/ast_semantic_value.spl`,
lines 610 and 2460: `ast_semantic_encode_expr(b_Array_f1, state)` on an
`Expr?`, then its `IntLit` arm. This is not verified. Any fix there needs a new
Stage 2 to prove, because the seed interpreter does not reproduce native
payload layout.

## Gap this exposed

The phase-2 surface pass has no ICE breadcrumb. When a module-attributable crash
happens there, it is not turned into one FAILED module. It kills every owner,
and `stop_dispatch` stops the HIR pool. That is the part of "go to the end
through crashes" that is still open.

## Related

The worker change on the same day (`driver_hir_worker_parse_verdict_v1`)
handles the parse-error half. A surface-pass parse error now becomes a FAILED
row for that module, and the worker keeps going. It does not address this
SIGSEGV.

## Root cause (resolved 2026-11-13)

Not the `IntLit` arm, and not `Some(...)` alone. The generated encoder passes
a nil-guarded optional enum-payload binder straight into a typed callee:
`ast_semantic_value.spl` (old :610 / :2460)
`if b_Array_f1 == nil: ... else: ast_semantic_encode_expr(b_Array_f1, state)`.
MIR has no flow typing, so call arguments handed the callee the Option box.
The faulting load (`ldr x10, [x1, x14, lsl #3]`) is
`node.explicit_call_types[i]` read through the box. A literal-size field is
the only producer of a non-nil `TypeKind.Array` size: `flat_field_sized_type`,
`_FlatAstBridge/module_assembly.spl:237`, from af589940249. That is why
`[u8; N]` and `[u8]` built fine.

Miscompile, not a source bug: the seed interpreter gives the right answer for
the same shape, the seed JIT reads garbage for a Some-built payload, and the
candidate SIGSEGVs for both bare and Some. Record:
optional_struct_payload_narrowing_native_2026_11_13.md.

Fix:
- MIR call-argument unwrap (`option_record_argument_payload_v1`).
- Generator workaround: fold_gen projects every optional with `!`.
- Regenerated encoder.

Closure check: the Phase 2/3 bootstrap_main closure has no `[T; <int>]`
struct, class or trait field. Its source roots exclude src/os, and the only
src/lib hit, game3d/math.spl, is never imported. The full-CLI closure, which
includes `--source src/os`, reaches src/os/kernel/arch/arch_context.spl.
