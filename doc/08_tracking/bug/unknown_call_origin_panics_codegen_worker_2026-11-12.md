# Unknown MIR call origin aborts the whole staged native build (panic, not a unit error)

**Status:** OPEN (observed 2026-11-12, aarch64 Linux, bootstrap-fable run 13, row `compiler_cli_build`)
**Area:** compiler / MIR callable authority -> backends (cranelift, LLVM, native isel)

## Symptom

Stage 2 building the full CLI (3082 modules, staged codegen, cranelift)
reached codegen batch 23 (`app.ui.access_cli` .. `app.office.slides.slide`)
and the native-build worker died with signal 6:

```
MIR call target lacks proven source/runtime/foreign origin
error: native-build worker terminated with signal 6 before producing a binary; NOT a compile failure.
```

`mir_call_origin_uses_local_symbols` (`src/compiler/50.mir/mir_instruction_support.spl`)
`panic`s on `MirCallOrigin.Unknown`. It is called from the cranelift adapter
(`cl_translate_operand`, `cl_translate_call`), `isel_context.isel_call_symbol`
and four LLVM `core_codegen` sites. A single unproven callee in one function
therefore kills the process: the ~2900 modules after it get no codegen and
no failure census.

## Trigger fixed separately

The Unknown origin in run 13 came from a HIR scoping leak, fixed in the same
change as this record: enum struct-variant payload fields were bound
lexically in module scope, so `UIEvent.MouseEvent(button: text)` shadowed
`common.ui.builder.button` inside every class method lowered after the enum
(`app.office.word.word_app` `WordApp.build_ui`). MIR saw a `Field` symbol
as the callee and correctly refused to call it Source. Pinned by
`test/01_unit/compiler/mir/method_scope_call_origin_spec.spl`.

## What remains (this record)

The fail-stop shape is still wrong. Unknown must stay a hard error (mapping
it to Source would be fail-open), but it should be a per-unit compile error
naming the function and the callee, so staged codegen keeps going and the
build fails at the end with the full census — the way a cranelift verifier
rejection of one function already becomes `[native-compile-failed] <module>`.

Candidate shapes, both larger than the ~30-line budget of the fixing lane:

1. A mandatory MIR verify rule (like `MIRV-001n`): `MirFnVerifier.use_operand`
   reports a `Const(Str, FuncPtr)` operand with `call_origin == Unknown`.
   Needs a registry row in `config/compiler/mir_verify_rules.sdn`,
   `mir_verify_baseline.sdn`, `mir_verify_levels.spl` (rules list, mandatory
   set, level map) and `mir_verify_rule_registry_spec.spl` updates. Caveat:
   without `SIMPLE_NATIVE_GO_TO_END=1` a verify failure is sticky in
   `native_staged_codegen_flush_v1` (`verify_failed` is reset only under
   go-to-end), so every later batch would skip codegen — better than signal 6,
   but not a full census. Also check the MIR interpreter and borrow-check
   lanes, which tolerate Unknown today.
2. Backend-local: the cranelift adapter's `compile_function` returns false
   (-> `Failed to compile function: <fn>` -> per-module `CompileFailed`)
   after printing the callee, instead of panicking; same for LLVM and isel.
   Requires threading a failure flag out of `cl_translate_operand` /
   `cl_translate_call`.

## Reproduction

With the run-13 Stage 2 binary, from a tree that does NOT carry the HIR
fix, `SIMPLE_BOOTSTRAP=1 <stage2> native-build src/app/office/word/word_app.spl
--backend=cranelift --low-memory --entry-closure --threads 1 --cache-dir <d> -o <o>`
aborts in ~15 s (EXIT=134). Any future Unknown producer has the same effect.
