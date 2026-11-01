# inferarm MIR failure (2026-10-31)

## Root bug
Stage3 build (stage2 compiling `src/app/cli/bootstrap_main.spl`, whole-program closure) fails MIR lowering with
`unsupported MIR type kind [infer-arm]: unresolved inference variable Infer(id=0, generation=0) reached lower_type`
(src/compiler/50.mir/_MirLowering/function_lowering.spl ~1338-1354). Shape: an un-annotated empty-array local
(`var x = []`) later filled by `.push(...)` keeps an `Infer` element type. Reduced single-module probes with the pinned stage2
(plain and with SIMPLE_BOOTSTRAP/ARENA_DECLS env) do NOT reproduce it; it only appears in the full stage3 closure.

## Workaround sites (annotate the local with its element type; behaviour unchanged)
Removal condition: remove once the root fix is in a stage2 used for bootstrapping.

- src/compiler/10.frontend/desugar/poll_generator.spl:155
- src/compiler/10.frontend/desugar/poll_generator.spl:292
- src/compiler/10.frontend/desugar/poll_generator.spl:307
- src/compiler/10.frontend/desugar/state_enum.spl:256
- src/compiler/10.frontend/desugar/state_enum.spl:303
- src/compiler/10.frontend/desugar/suspension_analysis.spl:580
- src/lib/common/format_utils.spl:398
- src/lib/common/text_advanced.spl:67
- src/lib/common/text_advanced.spl:283
- src/lib/common/text_advanced.spl:462
- src/lib/common/text_advanced.spl:504
- src/lib/common/text_advanced.spl:530
- src/lib/common/text_advanced.spl:533
- src/lib/common/text_advanced.spl:659
- src/lib/nogc_async_mut/database/bug.spl:370
- src/lib/nogc_async_mut/database/bug.spl:390
- src/lib/nogc_async_mut/env/paths.spl:215
- src/lib/nogc_async_mut/file_system/path_ops.spl:205
- src/lib/nogc_async_mut/sosix/host_facade.spl:253
- src/lib/nogc_sync_mut/env/paths.spl:212

## Status (2026-11-01 re-check)

**Status:** open, not reproducible outside the full stage3 closure.
Seed-hosted in-process pure-Simple HIR+MIR re-check
(`test/01_unit/compiler/50.mir/infer_empty_array_push_spec.spl`): `var x = []` +
`.push(...)` (while / for loops, `.join`) lowers with no `[infer-arm]` diagnostic.
The single-module path does not exhibit the bug; whether the full closure still does
must be decided by a stage3 build without the annotations (phase 3 owner).
Revert-ready: unknown — only after a full-closure stage3 build passes without them.
