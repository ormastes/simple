# stage3_bootstrap_fixed_lower_module_segv_2026-10-11

Status: FIX COMMITTED (source); native validation PENDING a stage-2 rebuild that contains it.
No source workaround exists for a stage 2 built without the fix.

## Symptom

Phase 3 (frozen stage2 5d97a3dc, built by the Rust seed from tree 5dd9df1faf7; compiling
`src/app/cli/bootstrap_main.spl`, 1159 modules) passed HIR and monomorphization, then died:

    [BOOTSTRAP-PHASE] aot:lower_to_mir:start
    [WARN] stage3 bootstrap-flat pipeline active at mir:bootstrap_fixed: ...
    [BOOTSTRAP-PHASE] aot:bootstrap_fixed:start module=app.cli.bootstrap_main functions=31
    <process exit 139>

No `[mir-lower]` line follows, although `SIMPLE_COMPILER_PHASE_PROFILE=1` enables that trace and
`lower_module` prints `[mir-lower] lower_module:start` before its first function.

## Reproduction (3 seconds)

Replace `src/app/cli/bootstrap_main.spl` in a scratch checkout with a 14-line file (one extern,
three functions) and run the phase-3 command (`SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE3=1`,
`--entry src/app/cli/bootstrap_main.spl --entry-closure --mode dynload`). Same exit 139 at
`aot:bootstrap_fixed:start ... functions=4`. The crash does not depend on the entry's content.

lldb (the binary has no symbols):

    Exception 0xc0000005 ... Access violation reading location 0x0003ff08
    ->  movq 0x8(%rax), %rax        ; rax = 0x3ff00, r8 = 0x3ffff
        testq %rax, %rax
        jle   ...

A length read (`+8`) followed by a loop guard, on a value that is not a heap object.

## Cause, as far as it is established

The fixed-entry branch of `lower_to_mir` (`src/compiler/80.driver/driver_pipeline_lowering.spl`)
ended in

    var bootstrap_mir = bootstrap_lowering.lower_module(bootstrap_hir)

Established by measurement on the same binary and the same 14-line module:

- with `SIMPLE_BOOTSTRAP_STAGE4=1` the gate skips the fixed branch and the direct branch runs
  `direct_lowering.lower_module_transient_scoped(direct_hir, providers, direct_idx == 0)`.
  That lowers the module (`[mir-lower] lower_function:start main`, `... functions=3`).
- so `MirLowering.lower_module` itself is sound in this binary; what crashes is reaching it
  through the fixed branch's call.

Two properties distinguish the crashing call from the working one, and they were NOT separated
(the binary cannot be instrumented):

1. it omits both defaulted parameters (`providers: [HirModule] = []`, `is_entry_module: bool = true`);
2. `lower_module` with exactly one argument is also `HirLowering.lower_module(module: ParserModule)`.
   `driver_hir_pipeline_lowering.spl` already records that a plain `lowering.lower_module(...)`
   "mis-dispatches on the stage4 binary (same-name sibling on MirLowering)" and uses the
   uniquely named `lower_parser_module_unstub` for that reason.

Either a garbage `providers` array or a dispatch into the HIR sibling produces a length read on
a non-object. The fix removes both properties at once.

## Fix

- `MirLowering.lower_bootstrap_entry_module(module)` (`src/compiler/50.mir/_MirLowering/module_lowering.spl`):
  a name no other class declares, forwarding `self.lower_module(module, no_providers, true)`
  with every argument explicit - the call shape the direct lane proves on the native binary.
- the fixed branch calls it.

No behaviour change on the seed: `test/01_unit/compiler/driver/stage3_bootstrap_fixed_entry_lowering_spec.spl`
pins equal output against `lower_module(hir, [], true)` and pins the call shape in both files.

## What this lane emits (answering "is only the entry compiled?")

Yes. In the stage3 bootstrap-fixed lane the compiler MIR-lowers `app.cli.bootstrap_main` only
(the `[WARN] stage3 bootstrap-flat` banner), `compile_bootstrap_context_to_native`
(`src/compiler/80.driver/driver_bootstrap.spl`) emits one object,
`<output>.app.cli.bootstrap_main.o`, and `link_llvm_native([obj_path], ...)` links that single
object. The other 1158 modules are parsed, HIR-lowered and checked, but no MIR and no object is
produced for them here; their code has to come from the libraries on `--runtime-path`
(`simple_compiler_backfill.lib`, `simple_native_all.lib`). Read from source, not confirmed by a
completed link.

## Open

- Which of the two properties is the actual trigger.
- Whether the same shape exists elsewhere: a census of one-argument calls to methods that
  have a same-named sibling on another class, or that omit defaulted array parameters, has not
  been done.
- The underlying seed native-codegen defect is not fixed by this change.
