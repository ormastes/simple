# Compiler Driver Layer Expert

Mission-critical V2 bootstrap/admission status is owned by
`doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`; its active owner
failure is `doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md`.

## Role

Own source discovery, import closure, phase orchestration, execution-mode
selection, and compiler-driver performance under `src/compiler/80.driver/`.

## Source-loading invariant

- `Check` mode loads only the requested checking scope.
- `Interpret` mode keeps the explicit entry bounded and lets the interpreter
  module loader resolve imports lazily.
- Native entry-closure mode loads the transitive closure selected by
  `SIMPLE_NATIVE_BUILD_ENTRY` and suppresses whole-project bulk loading.
- Other project compilation modes may bulk-load the self-hosted compiler roots
  where their global compilation model requires it.

Do not reuse the native-only entry-closure environment flag as a shortcut for
interpretation: downstream HIR/MIR branches attach native/bootstrap semantics
to it. Keep the interpret exclusion explicit in
`driver_source_pipeline_loading.spl`.

## Performance evidence

The compiler-loader negative-cache and packed-byte performance handoff lives at
`doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md` (plan content
accepted; operational reconciliation pending; feature verification blocked).
Preserve its
distinction between facade failed-existence probes and filesystem syscalls, its
caller-sensitive cache key and reset generation, and its admitted-self-hosted
evidence rule. Live feature verification remains blocked by two distinct
prerequisites: the older deployed candidate's wrapper/help admission segfault,
and historical lane-A Stage3 context corruption after a clean 603-file parse.
Fresh r3 remains unproved: its first process was intentionally stopped before
Stage 2 admission so review corrections could be source-frozen; partial output
is not authority and no verdict/cycle was consumed. The latter is tracked at
`doc/08_tracking/bug/build11_stage3_compile_context_corruption_2026-08-14.md`.

For a one-file interpreted entry, measure wall time and max RSS through the
normal `bin/simple` command. A run that never reaches user code is source-loader
cost, not workload cost. Preserve the normal CPU guard; raising it is diagnostic
only and cannot be passing evidence.

Focused contract:
`test/01_unit/compiler/driver/interpret_lazy_project_sources_spec.spl`.
MCP end-to-end witness:
`test/02_integration/app/mcp_stdio_integration_spec.spl`.

Typed-storage native codegen freezes deep-copied module-qualified evidence
before cache lookup. The parent then creates class-handle MIR+storage capsules;
the builder callback sees only the frozen batch and module name. Revalidate
complete MIR/storage identity before and after codegen, bind object bytes and
size in the result receipt, and publish cache checkpoints only through the
parent completion hook. Do not call this real concurrency: the current
builder branch batches sequentially, and process workers need a complete codec.

## Separate RV64 Stage 3 MIR receiver corruption handoff (2026-08-14)

This is not the Build11 compiler-loader frontier above. The RV64 prerequisite
bootstrap reaches HIR with zero errors, then its
Stage 3 log ends in MIR method-call lowering with an impossible receiver local
ID. Inspect `method_calls_literals.spl` receiver resolution/writeback and the
`value_struct_layout.spl` push-heavy caller shapes. Do not claim the direct
`CompileContext.error_count_value` reads fixed the root cause; require an exact
native reproducer, adjacent aggregate/method-call regression, and a fresh
Stage 4 essential-tools receipt. Tracking:
`doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md`.
